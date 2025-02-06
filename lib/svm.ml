open Base

module GenSymbol = struct
  module T = struct
    type t = int
  end

  module S = State.Make (T)

  let next hint =
    let n = S.get () in
    S.put (n + 1);
    Fmt.str "%s%d" hint n

  let get = S.get
  let put = S.put
  let run = S.run ~init:0
  let run_state = S.run_state ~init:0
end

module GenSymbolic = struct
  include GenSymbol

  let next : type a. a Solvable.Ty.t -> a Solvable.t =
   fun ty ->
    let hint = match ty with Bool -> "b$" | Z -> "int$" in
    let s = GenSymbol.next hint in
    Solvable.Sym (s, ty)
end

module VC = struct
  type t = { pre : Solvable.bool; post : Solvable.bool } [@@deriving fields]

  let pp =
    Fmt.(record [ field "pre" pre Solvable.pp; field "post" post Solvable.pp ])

  let init = Solvable.DSL.{ pre = tt; post = tt }
end

module VM = struct
  module S = State.Make (VC)
  open Solvable
  open Solvable.DSL

  exception AssumeFalse
  exception AssertFalse

  (** Note: the client should not modify pre-conditions. Otherwise, we need to modify the VM to implement Rosette 4 (currently we implement Rosette 3 semantics)*)
  let assume = function
    | Const (true, _) -> ()
    | Const (false, _) -> raise AssumeFalse
    | b ->
        let vc = S.get () in
        S.put { vc with pre = vc.pre && b }

  let assert_ ?(guarded = true) = function
    | Const (true, _) -> ()
    | Const (false, _) -> raise AssertFalse
    | b ->
        let vc = S.get () in
        S.put
          { vc with post = (vc.post && if guarded then vc.pre ==> b else b) }

  let set_post = function
    | Const (true, _) -> ()
    | Const (false, _) -> raise AssertFalse
    | b ->
        let vc = S.get () in
        S.put { vc with post = b }

  let clear () = S.put DSL.{ pre = tt; post = tt }
  let pre () = (S.get ()).pre
  let post () = (S.get ()).post
  let vc () = S.get ()

  let if_ b t f =
    let vc : VC.t = S.get () in
    (* run true branch by assuming b *)
    let o1 =
      try
        Some
          (S.run_state
             (fun () ->
               assume b;
               t)
             ~init:{ pre = vc.pre; post = tt })
        (* unliked Rosette, non-VM exceptions are unhandled, and simply propagated upward *)
      with AssumeFalse | AssertFalse -> None
    in
    (* run false branch by assuming (not b) *)
    let o2 =
      try
        Some
          (S.run_state
             (fun () ->
               assume (not b);
               f)
             ~init:{ pre = vc.pre; post = tt })
        (* unliked Rosette, non-VM exceptions are unhandled, and simply propagated upward *)
      with AssumeFalse | AssertFalse -> None
    in
    (* extract post conditions, and default to (not path cond) if there was an exception *)
    let post1 =
      Option.(map ~f:(Fn.compose VC.post snd) o1 |> value ~default:(not b))
    in
    let post2 =
      Option.(map ~f:(Fn.compose VC.post snd) o2 |> value ~default:b)
    in
    assert_ ~guarded:false post1;
    assert_ ~guarded:false post2

  let bool' () = GenSymbolic.next Ty.Bool
  let z' () = GenSymbolic.next Ty.Z
  let int' = z

  let range ?lo ?hi () =
    let x = z' () in
    Option.iter lo ~f:(fun lo -> assert_ (x >= int lo));
    Option.iter hi ~f:(fun hi -> assert_ (x < int hi));
    x

  let ctx = Z3.mk_context [ ("model", "true"); ("proof", "false") ]
  let bool_sort = Z3.Boolean.mk_sort ctx
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx

  let of_ty : type a. a Solvable.Ty.t -> Z3.Sort.sort =
   fun ty -> match ty with Bool -> bool_sort | Z -> int_sort

  let solver = Z3.Solver.mk_solver ctx None
  let optimizer = Z3.Optimize.mk_opt ctx

  type result = UNSAT | SAT of Z3.Model.model | UNKNOWN

  let solve () =
    let { pre; post } : VC.t = S.get () in
    let q = pre ==> post in
    Logs.debug (fun m -> m "query: %a" Solvable.pp q);
    let status = Z3.Solver.check solver [ ToZ3.compile ctx q ] in
    match status with
    | Z3.Solver.UNSATISFIABLE -> UNSAT
    | Z3.Solver.SATISFIABLE ->
        SAT (Z3.Solver.get_model solver |> Option.value_exn)
    | Z3.Solver.UNKNOWN -> UNKNOWN

  let minimize e =
    let { pre; post } : VC.t = S.get () in
    let q = pre ==> post in
    Logs.debug (fun m -> m "query: %a" Solvable.pp q);
    let obj = ToZ3.compile ctx e in
    Logs.info (fun m -> m "objective: %s" (Z3.Expr.to_string obj));
    let handle = Z3.Optimize.minimize optimizer obj in
    Z3.Optimize.add optimizer [ ToZ3.compile ctx q ];
    let status = Z3.Optimize.check optimizer in
    match status with
    | Z3.Solver.UNSATISFIABLE -> UNSAT
    | Z3.Solver.SATISFIABLE ->
        let model = Z3.Optimize.get_model optimizer |> Option.value_exn in
        Logs.info (fun m ->
            m "lower: %s" (Z3.Expr.to_string (Z3.Optimize.get_lower handle)));
        Logs.info (fun m ->
            m "upper: %s" (Z3.Expr.to_string (Z3.Optimize.get_upper handle)));
        SAT model
    | Z3.Solver.UNKNOWN -> UNKNOWN

  let env ?min () =
    let result = match min with Some e -> minimize e | None -> solve () in
    match result with
    | SAT model ->
        Some
          {
            self =
              (fun (type a) x (ty : a Ty.t) : a value ->
                match
                  Z3.Model.eval model (Z3.Expr.mk_const_s ctx x (of_ty ty)) true
                with
                | Some v ->
                    let s = Z3.Expr.get_sort v in
                    if Z3.Sort.equal s bool_sort then
                      match ty with
                      | Bool ->
                          if Z3.Boolean.is_true v then VBool true
                          else if Z3.Boolean.is_false v then VBool false
                          else failwith "unsupported bool"
                      | _ ->
                          failwith
                            Fmt.(str "expected type %a, got bool" Ty.pp ty)
                    else if Z3.Sort.equal s int_sort then
                      match ty with
                      | Z -> VZ (Z3.Arithmetic.Integer.get_big_int v)
                      | _ ->
                          failwith
                            Fmt.(str "expected type %a, got int" Ty.pp ty)
                    else
                      failwith
                        Fmt.(str "unsupported sort %s" (Z3.Sort.to_string s))
                | _ -> failwith Fmt.(str "no value for symbol %a" string x));
          }
    | _ -> None

  let run ?(init = VC.init) f = GenSymbolic.run (fun () -> S.run f ~init)

  let run_state ?(init = VC.init) f =
    GenSymbolic.run_state (fun () -> S.run_state f ~init)
end
