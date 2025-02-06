open Base

module SBool = struct
  type t =
    | Const of bool
    | Sym of string
    | Not of t
    | And of t * t
    | Or of t * t
    | If of t * t * t

  let rec pp ppf =
    let open Fmt in
    function
    | Const b -> bool ppf b
    | Sym s -> string ppf s
    | Not b -> pf ppf "@[<hov 2>¬%a@]" pp b
    | And (b1, b2) -> pf ppf "@[<hov 2>%a@ ∧ %a@]" pp b1 pp b2
    | Or (b1, b2) -> pf ppf "@[<hov 2>%a@ ∨ %a@]" pp b1 pp b2
    | If (b1, b2, b3) -> pf ppf "@[<hov 2>ite(%a, %a, %a)@]" pp b1 pp b2 pp b3

  let tt = Const true
  let ff = Const false
  let const b = Const b
  let ( !! ) s = Sym s
  let not b = Not b
  let ( && ) b1 b2 = And (b1, b2)
  let ( || ) b1 b2 = Or (b1, b2)
  let ite b1 b2 b3 = If (b1, b2, b3)
end

type 'a t = Leaf : 'a -> 'a t | If : SBool.t * 'a t * 'a t -> 'a t

let rec pp ppa ppf =
  let open Fmt in
  function
  | Leaf a -> (box ppa) ppf a
  | If (b, t, f) ->
      pf ppf "@[<v>if %a@ then %a@ else %a@]" SBool.pp b (pp ppa) t (pp ppa) f

let leaf x = Leaf x
let if_ b t f = If (b, t, f)
let rec leftmost = function Leaf a -> a | If (_, t, _) -> leftmost t

type 'a compare = 'a -> 'a -> int

module Strat = struct
  type _ t =
    | Simple : (SBool.t -> 'a -> 'a -> 'a) -> 'a t
    | Sorted : 'idx compare * ('a -> 'idx) * ('idx -> 'a t) -> 'a t

  let simple f = Simple f
  let sorted compare idx proj = Sorted (compare, idx, proj)
  let id = Simple (fun _ a _ -> a)
  let sort (compare : 'a compare) : 'a t = sorted compare Fn.id (fun _ -> id)
  let int = sort Int.compare
  let bool = sort Bool.compare
  let sbool = simple (fun b (a1 : SBool.t) a2 -> If (b, a1, a2))

  (* Partial profunctor monkaS *)
  let rec bimap : 'a 'b. f:('a -> 'b) -> g:('b -> 'a) -> 'a t -> 'b t =
   fun ~f ~g -> function
    | Simple m -> Simple (fun c b1 b2 -> f (m c (g b1) (g b2)))
    | Sorted (compare, idx, proj) ->
        Sorted
          ( compare,
            Fn.compose idx g,
            fun i ->
              let t = proj i in
              bimap ~f ~g t )

  let either (a : 'a t) (b : 'b t) : ('a, 'b) Either.t t =
    Sorted
      ( Bool.compare,
        Either.is_first,
        function
        | true ->
            bimap ~f:Either.first
              ~g:(function Either.First x -> x | _ -> assert false)
              a
        | false ->
            bimap ~f:Either.second
              ~g:(function Either.Second x -> x | _ -> assert false)
              b )

  let compare_pair compare1 compare2 (a1, b1) (a2, b2) =
    if compare1 a1 a2 = 0 then compare2 b1 b2 else compare1 a1 a2

  let par f g (x, y) = (f x, g y)

  let rec pair (a : 'a t) (b : 'b t) : ('a * 'b) t =
    match (a, b) with
    | Simple ma, Simple mb ->
        Simple (fun c (a1, b1) (a2, b2) -> (ma c a1 a2, mb c b1 b2))
    | Simple _, Sorted (compare, idx, proj) ->
        Sorted (compare, Fn.compose idx snd, fun i -> pair a (proj i))
    | Sorted (compare, idx, proj), Simple _ ->
        Sorted (compare, Fn.compose idx fst, fun i -> pair (proj i) b)
    | Sorted (c1, idx1, proj1), Sorted (c2, idx2, proj2) ->
        Sorted
          ( compare_pair c1 c2,
            par idx1 idx2,
            fun (i1, i2) -> pair (proj1 i1) (proj2 i2) )
end

module Merge = struct
  type variant = N | SS | SI | IS | II

  type 'a term =
    | Value of 'a Strat.t * 'a t
    | If of variant * 'a Strat.t * SBool.t * 'a t * 'a t

  let rec merge (v : variant) (ms : 'a Strat.t) (c : SBool.t) (t : 'a t)
      (f : 'a t) : 'a t =
    match (v, ms, c, t, f) with
    | N, _, Const true, _, _ -> t
    | N, _, Const false, _, _ -> f
    | N, Simple s, _, Leaf t1, Leaf f1 -> Leaf (s c t1 f1)
    | N, Sorted _, _, Leaf _, Leaf _ -> merge SS ms c t f
    | N, Sorted _, _, If _, Leaf _ -> merge IS ms c t f
    | N, Sorted _, _, Leaf _, If _ -> merge SI ms c t f
    | N, Sorted _, _, If _, If _ -> merge II ms c t f
    | N, _, _, _, _ -> failwith "impossible"
    | SS, Sorted (compare, i, s), _, _, _ ->
        let ti = i (leftmost t) in
        let fi = i (leftmost f) in
        if compare ti fi < 0 then If (c, t, f)
        else if compare ti fi > 0 then If (Not c, f, t)
        else merge N (s ti) c t f
    | SS, _, _, _, _ -> failwith "impossible"
    | SI, Sorted (compare, i, s), _, _, If (fc, ft, ff) ->
        let ti = i (leftmost t) in
        let fti = i (leftmost ft) in
        let ffi = i (leftmost ff) in
        if compare fti ffi = 0 then merge SS ms c t f
        else if compare ti fti < 0 then If (c, t, f)
        else if compare ti fti = 0 then
          let t' = merge N (s ti) c t ft in
          If (Or (c, fc), t', ff)
        else
          let f' = merge N ms c t ff in
          If (And (Not c, fc), ft, f')
    | SI, _, _, _, _ -> failwith "impossible"
    | IS, _, _, _, _ -> merge SI ms c f t
    | II, Sorted (compare, i, s), _, If (tc, tt, tf), If (fc, ft, ff) ->
        let tti = i (leftmost tt) in
        let tfi = i (leftmost tf) in
        let fti = i (leftmost ft) in
        let ffi = i (leftmost ff) in
        if compare tti tfi = 0 then merge SI ms c t f
        else if compare fti ffi = 0 then merge IS ms c t f
        else if compare tti fti < 0 then
          let f' = merge N ms c tf f in
          If (And (c, tc), tt, f')
        else if compare tti fti = 0 then
          let t' = merge N (s tti) c tt ft in
          let f' = merge N ms c tf ff in
          If (SBool.If (c, tc, fc), t', f')
        else
          let f' = merge N ms c t ff in
          If (And (Not c, fc), ft, f')
    | II, _, _, _, _ -> failwith "impossible"

  let run s = merge N s
end

module Test = struct
  let t1 =
    let open SBool in
    if_ !!"c1"
      (leaf (1, (1, !!"u")))
      (if_ !!"c2"
         (leaf (1, (2, !!"v")))
         (if_ !!"c3" (leaf (2, (3, !!"w"))) (leaf (2, (4, !!"x")))))

  let t2 =
    let open SBool in
    if_ !!"c4" (leaf (1, (1, !!"y"))) (leaf (9, (1, !!"z")))

  let strat = Strat.(pair int (pair int sbool))

  let t3 =
    let open SBool in
    Merge.run strat !!"c" t1 t2

  let ppa =
    Fmt.(parens @@ pair int ~sep:comma (parens @@ pair int ~sep:comma SBool.pp))

  let () = Fmt.pr "%a\n%!" (pp ppa) t3
end
