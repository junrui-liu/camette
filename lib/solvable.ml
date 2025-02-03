open Base

module Uty = struct
  type t = Bool | Z
end

module Ty = struct
  type _ t = Bool : bool t | Z : Z.t t

  let pp : type a. a t Fmt.t =
   fun ppf x ->
    match x with Bool -> Fmt.string ppf "bool" | Z -> Fmt.string ppf "int"

  type e = Ex : 'a t -> e

  let to_uty : type a. a t -> Uty.t = function Bool -> Uty.Bool | Z -> Z
  let of_uty : Uty.t -> e = function Uty.Bool -> Ex Bool | Z -> Ex Z
end

type boolop = And | Or [@@deriving compare, equal]

let pp_boolop = Fmt.using (function And -> "&&" | Or -> "||") Fmt.string

type zop = Add | Sub | Mul [@@deriving compare, equal]

let pp_zop =
  Fmt.using (function Add -> "+" | Sub -> "-" | Mul -> "*") Fmt.string

type zcomp = Lt | Leq | Gt | Geq [@@deriving compare, equal]

let pp_zcomp =
  Fmt.using
    (function Lt -> "<" | Leq -> "<=" | Gt -> ">" | Geq -> ">=")
    Fmt.string

let pp_z = Fmt.using Z.to_string Fmt.string

type _ t =
  | Sym : Symbol.t * 'a Ty.t -> 'a t
  | Const : 'a * 'a Ty.t -> 'a t
  | If : bool t * 'a t * 'a t -> 'a t
  | Neg : bool t -> bool t
  | Implies : bool t * bool t -> bool t
  | Boolop : boolop * bool t list -> bool t
  | Zop : zop * Z.t t list -> Z.t t
  | Zcomp : zcomp * Z.t t * Z.t t -> bool t
  | Eq : 'a t * 'a t -> bool t

let rec pp : type a. a t Fmt.t =
  let open Fmt in
  fun ppf -> function
    | Sym (s, _) -> pf ppf "%a" Symbol.pp s
    | Const (c, Bool) -> pf ppf "%b" c
    | Const (c, Z) -> pf ppf "%a" pp_z c
    | If (c, t, f) -> pf ppf "@[<2>(ite %a@ %a@ %a)@]" pp c pp t pp f
    | Neg x -> pf ppf "@[<2>(!@ %a)@]" pp x
    | Implies (x, y) -> pf ppf "@[<2>(==> %a@ %a)@]" pp x pp y
    | Boolop (op, xs) ->
        pf ppf "@[<2>(%a@ %a)@]" pp_boolop op (box @@ list ~sep:sp pp) xs
    | Zop (op, xs) ->
        pf ppf "@[<2>(%a@ %a)@]" pp_zop op (box @@ list ~sep:sp pp) xs
    | Zcomp (op, x, y) -> pf ppf "@[<2>(%a@ %a@ %a)@]" pp_zcomp op pp x pp y
    | Eq (x, y) -> pf ppf "@[<2>(= %a@ %a)@]" pp x pp y

let rec to_ty : type a. a t -> a Ty.t = function
  | Sym (_, p) -> p
  | Const (_, p) -> p
  | If (_, e, _) -> to_ty e
  | Neg _ -> Ty.Bool
  | Implies _ -> Ty.Bool
  | Boolop _ -> Ty.Bool
  | Zop _ -> Ty.Z
  | Zcomp _ -> Ty.Bool
  | Eq _ -> Ty.Bool

module DSL = struct
  let const x ty = Const (x, ty)
  let tt = const true Ty.Bool
  let ff = const false Ty.Bool
  let bool x = const x Ty.Bool
  let z n = const n Ty.Z
  let int n = z (Z.of_int n)
  let sbool x = Sym (x, Ty.Bool)
  let sz x = Sym (x, Ty.Z)

  let if_ cond t f =
    match cond with
    | Const (true, _) -> t
    | Const (false, _) -> f
    | _ -> If (cond, t, f)

  let not x =
    match x with
    | Const (a, _) -> const (not a) Ty.Bool
    | Neg x -> x
    | _ -> Neg x

  let equal : type a. a t -> a t -> bool t =
   fun x y ->
    match (x, y) with
    | Const (a, Bool), Const (b, _) -> const Bool.(equal a b) Ty.Bool
    | Const (a, Z), Const (b, Z) -> const Z.(equal a b) Ty.Bool
    | _, _ -> Eq (x, y)

  (** Remove duplicates *)
  let dedup =
    List.fold_right ~init:[] ~f:(fun x acc ->
        match x with
        | Sym (x, ty) ->
            Sym (x, ty)
            :: List.filter acc ~f:(function
                 | Sym (y, _) -> Base.not (Symbol.equal x y)
                 | _ -> true)
        | _ -> x :: acc)

  (** Remove inverses like both x and not x*)
  let remove_inv bs =
    bs |> dedup
    |> List.fold_right ~init:(false, []) ~f:(fun e (has_inv, res) ->
           match e with
           | Sym (x, _) ->
               let found =
                 List.exists res ~f:(function
                   | Neg (Sym (y, _)) -> Symbol.equal x y
                   | _ -> false)
               in
               ( Base.(has_inv || found),
                 if found then
                   List.filter res ~f:(function
                     | Neg (Sym (y, _)) -> Base.not (Symbol.equal x y)
                     | _ -> true)
                 else e :: res )
           | Neg (Sym (x, _)) ->
               let found =
                 List.exists res ~f:(function
                   | Sym (y, _) -> Symbol.equal x y
                   | _ -> false)
               in
               ( Base.(has_inv || found),
                 if found then
                   List.filter res ~f:(function
                     | Sym (y, _) -> Base.not (Symbol.equal x y)
                     | _ -> true)
                 else e :: res )
           | _ -> (has_inv, e :: res))

  let and_ =
    let rec pe : bool t list -> [ `Const of bool | `Unknown of bool t list ] =
      function
      | [] -> `Const true
      | x :: ys -> (
          let x' =
            match x with
            | Const (a, _) -> `Const a
            | Boolop (And, xs) -> `Unknown xs
            | _ -> `Unknown [ x ]
          in
          match (x', pe ys) with
          (* both are constants *)
          | `Const a, `Const b -> `Const (a && b)
          (* one of them is false *)
          | `Const false, _ | _, `Const false -> `Const false
          (* one of them is true *)
          | `Const true, zs | zs, `Const true -> zs
          (* both are unknown *)
          | `Unknown xs, `Unknown ys ->
              let has_inv, zs = remove_inv (xs @ ys) in
              if has_inv then `Const false else `Unknown zs)
    in
    fun xs ->
      match pe xs with
      | `Const b -> const b Ty.Bool
      | `Unknown [ e ] -> e
      | `Unknown es -> Boolop (And, es)

  let ( && ) x y = and_ [ x; y ]

  let or_ =
    let rec pe : bool t list -> [ `Const of bool | `Unknown of bool t list ] =
      function
      | [] -> `Const false
      | x :: ys -> (
          let x' =
            match x with
            | Const (a, _) -> `Const a
            | Boolop (Or, xs) -> `Unknown xs
            | _ -> `Unknown [ x ]
          in
          let ys = pe ys in
          match (x', ys) with
          (* both are constants *)
          | `Const a, `Const b -> `Const (a || b)
          (* one of them is true *)
          | `Const true, _ | _, `Const true -> `Const true
          (* one of them is false *)
          | `Const false, zs | zs, `Const false -> zs
          (* both are unknown *)
          | `Unknown xs, `Unknown ys -> `Unknown (xs @ ys))
    in
    fun xs ->
      match pe xs with
      | `Const b -> const b Ty.Bool
      | `Unknown [ e ] -> e
      | `Unknown es -> Boolop (Or, es)

  let ( || ) x y = or_ [ x; y ]
  let ( ==> ) x y = (not x) || y

  let add =
    let rec pe : Z.t t list -> [ `Const of Z.t | `Unknown of Z.t t list ] =
      function
      | [] -> `Const Z.zero
      | x :: ys -> (
          let x =
            match x with
            | Const (a, _) -> `Const a
            | Zop (Add, xs) -> `Unknown xs
            | _ -> `Unknown [ x ]
          in
          match (x, pe ys) with
          (* both are const *)
          | `Const a, `Const b -> `Const Z.(a + b)
          (* one of them is zero *)
          | `Const a, `Unknown ys when Z.(equal a zero) -> `Unknown ys
          | `Unknown ys, `Const b when Z.(equal b zero) -> `Unknown ys
          (* otherwise *)
          | `Unknown xs, `Const b -> `Unknown (xs @ [ const b Ty.Z ])
          | `Const a, `Unknown ys -> `Unknown (const a Ty.Z :: ys)
          | `Unknown xs, `Unknown ys -> `Unknown (xs @ ys))
    in

    fun xs ->
      match pe xs with `Const b -> const b Ty.Z | `Unknown es -> Zop (Add, es)

  let ( + ) x y = add [ x; y ]

  let sub =
    let rec pe = function
      | [] -> `Const Z.zero
      | x :: ys -> (
          let x =
            match x with
            | Const (a, _) -> `Const a
            | Zop (Sub, xs) -> `Unknown xs
            | _ -> `Unknown [ x ]
          in
          match (x, pe ys) with
          (* both are const *)
          | `Const a, `Const b -> `Const Z.(a - b)
          (* pe ys is zero *)
          | `Unknown xs, `Const b when Z.(equal b zero) -> `Unknown xs
          (* otherwise *)
          | `Const a, `Unknown ys -> `Unknown (const a Ty.Z :: ys)
          | `Unknown xs, `Const b -> `Unknown (xs @ [ const b Ty.Z ])
          | `Unknown xs, `Unknown ys -> `Unknown (xs @ ys))
    in
    fun xs ->
      match pe xs with `Const b -> const b Ty.Z | `Unknown es -> Zop (Sub, es)

  let ( - ) x y = sub [ x; y ]

  let mul =
    let rec pe = function
      | [] -> `Const Z.one
      | x :: ys -> (
          let x =
            match x with
            | Const (a, _) -> `Const a
            | Zop (Mul, xs) -> `Unknown xs
            | _ -> `Unknown [ x ]
          in
          match (x, pe ys) with
          (* both are const *)
          | `Const a, `Const b -> `Const Z.(a * b)
          (* one of them is zero *)
          | `Const a, _ when Z.(equal a zero) -> `Const Z.zero
          | _, `Const b when Z.(equal b zero) -> `Const Z.zero
          (* one of them is one *)
          | `Const a, `Unknown ys when Z.(equal a one) -> `Unknown ys
          | `Unknown ys, `Const b when Z.(equal b one) -> `Unknown ys
          (* otherwise *)
          | `Const a, `Unknown ys -> `Unknown (const a Ty.Z :: ys)
          | `Unknown xs, `Const b -> `Unknown (xs @ [ const b Ty.Z ])
          | `Unknown xs, `Unknown ys -> `Unknown (xs @ ys))
    in
    fun xs ->
      match pe xs with `Const b -> const b Ty.Z | `Unknown es -> Zop (Mul, es)

  let ( * ) x y = mul [ x; y ]

  let ( < ) x y =
    match (x, y) with
    | Const (a, _), Const (b, _) -> const Z.(lt a b) Ty.Bool
    | _, _ -> Zcomp (Lt, x, y)

  let ( <= ) x y =
    match (x, y) with
    | Const (a, _), Const (b, _) -> const Z.(leq a b) Ty.Bool
    | _, _ -> Zcomp (Leq, x, y)

  let ( > ) x y =
    match (x, y) with
    | Const (a, _), Const (b, _) -> const Z.(gt a b) Ty.Bool
    | _, _ -> Zcomp (Gt, x, y)

  let ( >= ) x y =
    match (x, y) with
    | Const (a, _), Const (b, _) -> const Z.(geq a b) Ty.Bool
    | _, _ -> Zcomp (Geq, x, y)

  let ( = ) : type a. a t -> a t -> bool t =
   fun x y ->
    match (x, y) with
    | Const (a, Ty.Bool), Const (b, _) -> const Bool.(a = b) Ty.Bool
    | Const (a, Ty.Z), Const (b, Ty.Z) -> const Z.(equal a b) Ty.Bool
    | _, _ -> Eq (x, y)

  let ( <> ) x y = not (x = y)
  let max x y = if_ (x > y) x y

  let maxs xs =
    match xs with
    | [] -> failwith "maxs: empty list"
    | x :: xs -> List.fold ~f:max ~init:x xs

  let min x y = if_ (x < y) x y

  let mins xs =
    match xs with
    | [] -> failwith "mins: empty list"
    | x :: xs -> List.fold ~f:min ~init:x xs
end

module ToZ3 = struct
  open Z3
  open Z3.Expr
  open Z3.Arithmetic
  open Z3.Boolean

  let compile : type a. context -> a t -> expr =
   fun ctx ->
    let rec go : type a. a t -> expr = function
      | Sym (x, Bool) -> mk_const ctx (Symbol.mk_string ctx x)
      | Sym (x, Z) -> Integer.mk_const ctx (Symbol.mk_string ctx x)
      | Const (x, Bool) -> mk_val ctx x
      | Const (x, Z) -> Integer.mk_numeral_i ctx (Z.to_int x)
      | If (c, t, f) -> mk_ite ctx (go c) (go t) (go f)
      | Neg x -> mk_not ctx (go x)
      | Boolop (op, xs) ->
          let mk = match op with And -> mk_and | Or -> mk_or in
          mk ctx (List.map ~f:go xs)
      | Implies (x, y) -> mk_implies ctx (go x) (go y)
      | Zop (op, xs) ->
          let mk =
            match op with Add -> mk_add | Sub -> mk_sub | Mul -> mk_mul
          in
          mk ctx (List.map ~f:go xs)
      | Zcomp (Lt, x, y) -> mk_lt ctx (go x) (go y)
      | Zcomp (Leq, x, y) -> mk_le ctx (go x) (go y)
      | Zcomp (Gt, x, y) -> mk_gt ctx (go x) (go y)
      | Zcomp (Geq, x, y) -> mk_ge ctx (go x) (go y)
      | Eq (x, y) -> mk_eq ctx (go x) (go y)
    in
    go
end

type _ value = VBool : bool -> bool value | VZ : Z.t -> Z.t value
type env = { self : 'a. Symbol.t -> 'a Ty.t -> 'a value }

let eval : type a. env -> a t -> a =
 fun env ->
  let rec helper : type a. a t -> a = function
    | Sym (x, ty) -> (
        match (ty, env.self x ty) with
        | Bool, VBool b -> b
        | Z, VZ z -> z
        | _ -> failwith "type mismatch")
    | Const (x, _) -> x
    | If (c, t, f) -> if helper c then helper t else helper f
    | Neg x -> not (helper x)
    | Implies (x, y) -> (not (helper x)) || helper y
    | Boolop (op, xs) ->
        let o = match op with And -> ( && ) | Or -> ( || ) in
        List.fold ~f:(fun acc x -> o acc (helper x)) ~init:true xs
    | Zop (op, xs) ->
        let o =
          match op with Add -> Z.( + ) | Sub -> Z.( - ) | Mul -> Z.( * )
        in
        List.fold ~f:(fun acc x -> o acc (helper x)) ~init:Z.zero xs
    | Zcomp (op, x, y) ->
        let o =
          match op with Lt -> Z.lt | Leq -> Z.leq | Gt -> Z.gt | Geq -> Z.geq
        in
        o (helper x) (helper y)
    | Eq (x, y) -> (
        match (to_ty x, to_ty y) with
        | Bool, Bool -> Bool.(equal (helper x) (helper y))
        | Z, Z -> Z.equal (helper x) (helper y)
        | _, _ ->
            (* Why can't OCaml refute this case? *)
            failwith "type mismatch")
  in
  helper

type nonrec bool = bool t
type nonrec z = Z.t t
type int = z
