open Base
open Camette

let () =
  Logs.set_reporter (Logs.format_reporter ());
  Logs.set_level (Some Logs.Error)

let time f =
  let t = Stdlib.Sys.time () in
  let r = f () in
  (Stdlib.Sys.time () -. t, r)

module Cell = struct
  (** Table cell *)
  type t = Const of Z.t | Var of string | Empty [@@deriving equal]

  let pp fmt = function
    | Const c -> Fmt.pf fmt "%s" (Z.to_string c)
    | Var v -> Fmt.pf fmt "%s" v
    | Empty -> Fmt.pf fmt "empty"

  type t' = t Union.t
  (** Symbolic cell *)

  let pp_t' fmt c = Union.pp pp fmt c
  let eval env c = Union.eval env c
end

module Alpha = struct
  type 'a f = 'a Map.M(Int).t
  (** Cell assignment *)

  let pp_map pp_k pp_v =
    Fmt.(
      using Map.to_alist (vbox @@ list (box @@ pair pp_k ~sep:(any ": ") pp_v)))

  let pp_f pp_v fmt alpha = pp_map Fmt.int pp_v fmt alpha

  type t = Cell.t f

  let pp fmt alpha = pp_f Cell.pp fmt alpha

  type t' = Cell.t' f
  (** Symbolic cell assignment *)

  let pp_t' fmt alpha = pp_f Cell.pp_t' fmt alpha
  let eval env (t' : t') = Map.map t' ~f:(Cell.eval env)
end

module Trace = struct
  module Expr = struct
    type t = Const of Z.t | Var of string | Sub of t * t

    let rec pp : t Fmt.t =
      let open Fmt in
      fun ppf -> function
        | Const c -> pf ppf "%s" (Z.to_string c)
        | Var v -> pf ppf "%s" v
        | Sub (x, y) -> pf ppf "@[<2>(%a@ - %a)@]" pp x pp y
  end

  module Gate = struct
    type t = Constrain of Expr.t | Star of string

    let pp ppf = function
      | Constrain e -> Fmt.pf ppf "constrain(%a)" Expr.pp e
      | Star x -> Fmt.pf ppf "star(%s)" x
  end

  type t = Gate.t list

  let pp = Fmt.(vbox @@ list ~sep:cut (box @@ Gate.pp))
end

module Row = Int

module Circuit = struct
  module Gate = struct
    type t = Const of Zz.t | Ref of Row.t | Sub of t * t
    [@@deriving equal, compare, sexp]

    let const c = Const c
    let ref r = Ref r
    let ( - ) x y = Sub (x, y)

    let rec pp : t Fmt.t =
      let open Fmt in
      fun ppf -> function
        | Const c -> pf ppf "%s" (Z.to_string c)
        | Ref i -> pf ppf "[%d]" i
        | Sub (x, y) -> pf ppf "@[<2>(%a@ - %a)@]" pp x pp y
  end

  module Selector = struct
    type entry = Row.t * Gate.t

    let pp_entry =
      let open Fmt in
      box @@ pair Fmt.int ~sep:(any " : ") Gate.pp

    type t = entry list
    type t' = entry Union.t list

    let eval : Solvable.env -> t' -> t =
     fun env t' -> List.map t' ~f:(fun u -> Union.eval env u)
  end

  type t = int * Gate.t list * Selector.t
  type t' = int * Gate.t list * Selector.t'

  let eval : Solvable.env -> t' -> t =
   fun env (i, gs, sel) -> (i, gs, Selector.eval env sel)

  let pp : t Fmt.t =
    let open Fmt in
    using (fun (_, _, sel) -> sel) (vbox @@ list Selector.pp_entry)

  let pp_t' : t' Fmt.t =
    let open Fmt in
    using
      (fun (_, _, sel) -> sel)
      (vbox @@ list @@ box @@ Union.pp ~swap:true Selector.pp_entry)
end

type row' = Row.t Union.t

let get_row (alpha' : Alpha.t') ~(f : Cell.t -> bool) : row' =
  let open Union in
  Map.fold alpha' ~init:void ~f:(fun ~key ~data acc ->
      Union.filter_map data ~f:(fun c -> if f c then Some key else None) || acc)

(** Return all possible rows that contain said constant *)
let row_const (c : Z.t) : Alpha.t' -> row' = get_row ~f:(Cell.equal (Const c))

(** Return all possible rows that contain said variable *)
let row_var (x : string) : Alpha.t' -> row' = get_row ~f:(Cell.equal (Var x))

(** Return all possible rows that contain an empty cell *)
let row_empty : Alpha.t' -> row' = get_row ~f:(Cell.equal Empty)

(** Return all possible rows that contain a non-empty cell *)
let row_nonempty : Alpha.t' -> row' =
  get_row ~f:(fun c -> not (Cell.equal c Empty))

(** Count the number of non-empty cells *)
let num_nonempty : Alpha.t' -> Solvable.z =
 fun alpha' ->
  let rs =
    alpha' |> Map.to_alist
    |> List.map ~f:(fun (_, c') ->
           (* Logs.debug (fun m -> m "num_nonempty: c': %a" (Union.pp Cell.pp) c'); *)
           let f =
             Union.filter_map c' ~f:(fun c ->
                 if Cell.equal c Empty then None else Some true)
           in
           (* Logs.debug (fun m ->
               m "num_nonempty: filtered: %a" (Union.pp Fmt.bool) f); *)
           let r = f |> Union.reduce in
           (* Logs.debug (fun m -> m "num_nonempty: reduced: %a" Solvable.pp r); *)
           r)
  in
  Logs.debug Fmt.(fun m -> m "nonempty rows: %a" (vbox @@ list Solvable.pp) rs);

  Solvable.DSL.add
    (List.map rs ~f:(fun r -> Solvable.DSL.(if_ r (int 1) (int 0))))

let ( @@@ ) f x =
  f x;
  x

let rec compile : Alpha.t' -> Trace.Expr.t -> Circuit.Gate.t Union.t =
 fun alpha' e ->
  Logs.debug (fun m -> m "compile %a" Trace.Expr.pp e);
  (fun r ->
    Logs.debug (fun m ->
        m "compile %a = %a" Trace.Expr.pp e (Union.pp Circuit.Gate.pp) r))
  @@@
  match e with
  | Const c ->
      let r = row_const c alpha' in
      Logs.debug (fun m ->
          m "row_const %a = %a" Z.pp_print c (Union.pp Row.pp) r);
      Union.(lift (Circuit.Gate.Const c) || map ~f:Circuit.Gate.ref r)
  | Var x ->
      let r = row_var x alpha' in
      Logs.debug (fun m -> m "row_var %s = %a" x (Union.pp Row.pp) r);
      Union.map ~f:Circuit.Gate.ref r
  | Sub (e1, e2) ->
      let g1 = compile alpha' e1 in
      let g2 = compile alpha' e2 in
      Union.map2 ~f:(fun x y -> Circuit.Gate.Sub (x, y)) g1 g2

let rec refs : Circuit.Gate.t -> Set.M(Int).t = function
  | Const _ -> Set.empty (module Int)
  | Ref i -> Set.singleton (module Int) i
  | Sub (x, y) -> Set.union (refs x) (refs y)

let shift (i : int) : Circuit.Gate.t -> Circuit.Gate.t =
  let rec go : Circuit.Gate.t -> Circuit.Gate.t = function
    | Circuit.Gate.Const c -> Const c
    | Ref j -> Ref (j + i)
    | Sub (x, y) -> Sub (go x, go y)
  in
  go

let relativize (g : Circuit.Gate.t) : int * Circuit.Gate.t =
  let rs = refs g in
  let i = Set.max_elt_exn rs in
  (i, shift (-i) g)

let compile_trace : Alpha.t' -> Trace.t -> Circuit.t' =
 fun alpha' tr ->
  let sel = [] in
  let gs, sel =
    List.fold tr ~init:([], sel) ~f:(fun (gs, sel) -> function
      | Constrain e ->
          let g' = compile alpha' e in
          let g'' = Union.map ~f:relativize g' in
          Union.one_of g'';
          let sel' = sel @ [ g'' ] in
          (gs @ Union.to_list g', sel')
      | Star x ->
          let r = row_var x alpha' in
          Union.one_of r;
          (gs, sel))
  in
  (0, gs, sel)

(* let vars = [ "x"; "y" ] *)
(* let const = [ Z.of_int 3 ] *)
module T (S : sig
  val vars : string list
  val consts : Z.t list
  val tr : Trace.t
  val m : int
end) =
struct
  open Svm
  open S

  let cells =
    List.map vars ~f:(fun v -> Cell.Var v)
    @ List.map consts ~f:(fun c -> Cell.Const c)
    @ [ Cell.Empty ]

  let cell' () = Union.choose cells
  let rows = List.init m ~f:Fn.id

  let alpha' () : Alpha.t' =
    List.map rows ~f:(fun i -> (i, cell' ())) |> Map.of_alist_exn (module Int)
  ;;

  Logs.debug (fun m -> m "VC: %a" VC.pp (VM.vc ()))

  (* test assignment *)
  let a = alpha' ();;

  Logs.debug (fun m -> m "a: %a" Alpha.pp_t' a)

  (* test compile *)
  let circ' = compile_trace a tr
  let obj = num_nonempty a;;

  Logs.debug (fun m -> m "sel: %a" Circuit.pp_t' circ');;
  Logs.debug (fun m -> m "VC: %a" VC.pp (VM.vc ()));;
  Logs.debug (fun m -> m "# nonempty: %a" Solvable.pp obj)

  let time, env =
    time (fun () ->
        match VM.env ~min:obj () with Some e -> e | None -> failwith "no env")

  let circ = Circuit.eval env circ';;

  Logs.info (fun m -> m "circ: %a" Circuit.pp circ)

  let alpha = Alpha.eval env a;;

  Logs.info (fun m -> m "alpha: %a" Alpha.pp alpha);;

  Logs.info (fun m ->
      m "num_nonempty: %a" Fmt.int
        (Map.length
           (Map.filter alpha ~f:(fun c -> not (Cell.equal c Cell.Empty)))))
  ;;

  Logs.app (fun m -> m "time: %f" time)
end

module Simple = struct
  let vars = [ "x"; "y" ]
  let consts = [ Z.of_int 3 ]
  let e = Trace.Expr.(Sub (Sub (Var "x", Const (Z.of_int 3)), Var "y"))

  (* let e = Trace.Expr.(Sub (Var "x", Const (Z.of_int 3))) *)
  let tr = Trace.Gate.[ Constrain e; Star "y" ]
  let m = 10
end

module Fib (S : sig
  val n : int
  val m : int
end) =
struct
  include S

  let vars =
    [ "x0"; "x1" ] @ List.init m ~f:(fun i -> "x" ^ Int.to_string (i + 2))

  let consts = []

  let rec gen_trace i =
    if i = n then []
    else
      let e =
        Trace.Expr.(
          Sub
            ( Sub
                (Var ("x" ^ Int.to_string (i + 2)), Var ("x" ^ Int.to_string i)),
              Var ("x" ^ Int.to_string (i + 1)) ))
      in
      Trace.Gate.(Constrain e :: gen_trace (i + 1))

  let tr = Trace.Gate.[ Star "x0"; Star "x1" ] @ gen_trace 0
end

module Fib5 = Fib (struct
  let n = 2
  let m = 10
end)

(* let () = Logs.info (fun m -> m "Fib5 trace: %a" Trace.pp Fib5.tr) *)

(* let f () =
     let module _ = T (Fib5) in
     ()

   let () = Svm.VM.run f *)

let test_fib n =
  let module F = Fib (struct
    let n = n
    let m = (n * 3) + 2
  end) in
  Svm.VM.run (fun () ->
      Logs.app (fun m -> m "Fib n=%d m=%d" n F.m);
      let module _ = T (F) in
      ())
;;

for i = 0 to 10 do
  test_fib i
done
