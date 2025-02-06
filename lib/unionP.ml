(* open Base

   module Void = struct
     type t = |
   end

   module Unit = struct
     type t = Unit of unit
   end

   module Product = struct
     type ('a, 'b) t = T of 'a * 'b
   end

   module Sum = struct
     type ('a, 'b) t = Inl of 'a | Inr of 'b
   end

   module Arr = struct
     type ('a, 'b) t = T of 'a * 'b
   end

   module Mu = struct
     type ('a, 'b) t = T of 'a * 'b
   end

   module Ty = struct
     type one = unit

     type _ t =
       | Zero : 'a t
       | One : one t
       | SumL : 'a t -> ('a, 'b) Sum.t t
       | SumR : 'b t -> ('a, 'b) Sum.t t
       | Product : 'a t * 'b t -> ('a * 'b) t

     let unfold_list :
         type a. a t -> a list -> a list t -> (one, a * a list) Sum.t t =
      fun t -> function
       | [] -> fun _ -> SumL One
       | _ :: _ -> fun r -> SumR (Product (t, r))
   end

   (* module Ty = struct

      module Idx = struct
        type (_, _) t = Z : ('a * 'g, 'a) t | S : ('g, 'a) t -> ('b * 'g, 'a) t

        let z = Z
        let one = S Z
        let s i = S i
      end
           type (_, _) t =
             | Void : ('g, Void.t) t
             | Unit : ('g, Unit.t) t
             | Sum : ('g, 'a) t * ('g, 'b) t -> ('g, ('a, 'b) Sum.t) t
             | Product : ('g, 'a) t * ('g, 'b) t -> ('g, ('a, 'b) Product.t) t
             | Fix : ('a * 'g, 'b) t -> ('g, ('a, 'b) Mu.t) t
             | Var : ('g, 'a) Idx.t -> ('g, 'a) t

           type _ inc = IZ : unit inc | IS : 'g inc -> ('a * 'g) inc

           type (_, _, _) append =
             | Nil : (unit, 'g, 'g) append
             | Cons : ('g1, 'g2, 'g) append -> ('a * 'g1, 'g2, 'a * 'g) append

           module Test = struct
             let rec add :
                 type g1 g2 g t.
                 g1 inc -> (g2, t) Idx.t -> (g1, g2, g) append -> (g, t) Idx.t =
              fun i n pf ->
               match i with
               | IZ -> ( match pf with Nil -> n)
               | IS i -> ( match pf with Cons pf' -> S (add i n pf'))

             let list (type a g) (t : (g, a) t) :
                 (g, (a list, (Unit.t, (a, a list) Product.t) Sum.t) Mu.t) t =
               let t' = add (IS IZ) in
               Fix (Sum (Unit, Product (t, Z)))
           end
         end *)

   module T = struct
     type _ t =
       (* | Empty : unit t *)
       | Leaf : 'a -> 'a t
       | Node : bool * 'a t * 'a t -> 'a t
       | Pair : ('a * 'b t) t -> ('a * 'b) t

     type _ ctx =
       | Top : 'a ctx
       | CNode : bool * 'a t * 'a ctx -> 'a ctx
       | CPairP : ('a * 'b) ctx -> ('a * 'b t) ctx
       | CPair : 'b ctx * ('a * 'b t) ctx -> ('a * 'b) ctx
     (* | CSum :
         ('a ctx * 'b t) option * ('a ctx * 'b t) option
         -> ('a, 'b) Sum.t ctx *)

     let leaf x = Leaf x
     let node b l r = Node (b, l, r)
     let pair x = Pair x

     (* let sum l r = Sum (l, r) *)
     let tree = pair (node true (leaf (1, leaf "hi")) (leaf (2, leaf "world")))

     let rec unzip : type a. a ctx -> a t -> a * a ctx =
      fun acc -> function
       (* | Empty -> ((), Top) *)
       | Leaf x -> (x, acc)
       | Node (b, l, r) -> unzip (CNode (b, r, acc)) l
       | Pair p ->
           let (x, b), r = unzip (CPairP acc) p in
           let y, c = unzip Top b in
           ((x, y), CPair (c, r))

     let rec merge (type a) (cond : bool) : a t -> a t -> a t =
       let helper : type a. a * a ctx -> a * a ctx -> a t = function
         | x, Top -> (
             function
             | y, Top ->
                 if Poly.(x = y) then Leaf x else if cond then Leaf x else Leaf y
             | y, CNode (b, r, ctx) ->
               if Poly.(x = y) then
                 )
       in
       fun l r -> helper (unzip Top l) (unzip Top r)

     (* | Sum (l, r) ->
         let x, l' = unzip l in
         let y, r' = unzip r in
         ((), SumL (l', r)) *)
   end *)
