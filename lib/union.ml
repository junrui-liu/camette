open Base

type 'a t = (Solvable.bool * 'a) list

let void = []

let pp ?(swap = false) (ppa : 'a Fmt.t) : 'a t Fmt.t =
  if swap then
    Fmt.(
      using
        (List.map ~f:(fun (x, y) -> (y, x)))
        (vbox @@ list @@ parens @@ box @@ pair ppa ~sep:(any " :- ") Solvable.pp))
  else
    Fmt.(vbox @@ list @@ parens @@ box @@ pair Solvable.pp ~sep:(any " . ") ppa)

let lift x = Solvable.DSL.[ (tt, x) ]

let if_ b xs ys =
  let open Solvable.DSL in
  match b with
  | Solvable.Const (true, _) -> xs
  | Solvable.Const (false, _) -> ys
  | _ ->
      List.map xs ~f:(fun (pre, x) -> (pre && b, x))
      @ List.map ys ~f:(fun (pre, y) -> (pre && not b, y))

let ( || ) xs ys =
  match (xs, ys) with
  | [], ys -> ys
  | xs, [] -> xs
  | _, _ -> if_ (Svm.VM.bool' ()) xs ys

let alt = List.fold_right ~init:void ~f:( || )
let choose xs = alt (List.map ~f:lift xs)

let prune =
  List.filter ~f:(function Solvable.Const (false, _), _ -> false | _ -> true)

let bind (t : 'a t) ~(f : 'a -> 'b t) : 'b t =
  List.concat_map t ~f:(fun (pre, x) ->
      List.map (f x) ~f:(fun (pre', y) -> (Solvable.DSL.(pre && pre'), y)))
  |> prune

let ( >>= ) x f = bind x ~f
let map (t : 'a t) ~(f : 'a -> 'b) = bind t ~f:(fun x -> lift (f x))
let map2 t1 t2 ~f = bind t1 ~f:(fun x -> map t2 ~f:(f x))

(* let reduce (t : Solvable.bool t) : Solvable.bool =
   let open Solvable.DSL in
   List.fold t ~init:tt ~f:(fun acc (pre, x) -> acc || (pre && x)) *)

(* let bmap t ~f = map t ~f |> reduce *)
let reduce (t : bool t) : Solvable.bool =
  List.filter_map t ~f:(fun (pre, b) -> if b then Some pre else None)
  |> Solvable.DSL.or_

let filterm (t : 'a t) ~f =
  List.map t ~f:(fun (pre, x) -> (Solvable.DSL.(pre && f x), x)) |> prune

let to_list t = List.map t ~f:snd
let view = List.map ~f:(fun (x, y) -> (y, x))

let filter_map (t : 'a t) ~f =
  List.filter_map t ~f:(fun (pre, x) ->
      match f x with Some y -> Some (pre, y) | _ -> None)

let one_of t =
  Svm.VM.assert_ (Solvable.DSL.or_ (List.map t ~f:(fun (pre, _) -> pre)))

let eval : Solvable.env -> 'a t -> 'a =
 fun env t ->
  (* FIX: do we need to assert every union is habitable? *)
  match
    List.find_map t ~f:(fun (pre, x) ->
        if Solvable.eval env pre then Some x else None)
  with
  | Some x -> x
  | None ->
      Logs.err
        Fmt.(
          fun m ->
            m "Union.eval: uninhabited union %a"
              (vbox @@ list @@ box @@ Solvable.pp)
              (List.map t ~f:fst));
      assert false

let dummy : type a. a Solvable.Ty.t -> a = function
  | Bool -> false
  | Z -> Z.zero

(** Internalize a union of solvable constants as a solvable expression *)
let internalize : type a. a Solvable.Ty.t -> a t -> a Solvable.t =
 fun ty ->
  List.fold_right
    ~init:(Solvable.Const (dummy ty, ty))
    ~f:(fun (pre, x) acc -> Solvable.DSL.if_ pre (Solvable.DSL.const x ty) acc)

let sum (t : Z.t t) : Solvable.z =
  List.fold_right t ~init:(Solvable.DSL.z Z.zero) ~f:(fun (pre, x) acc ->
      let y = Solvable.Sym (Svm.GenSymbol.next "int$", Z) in
      Svm.VM.assert_ (Solvable.DSL.equal y acc);
      let inc = Solvable.DSL.(z x + y) in
      (* let inc = Solvable.DSL.(z x + acc) in *)
      Solvable.DSL.if_ pre inc acc)
