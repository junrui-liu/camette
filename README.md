# Camette

Symbolic virtual machine a la [Rosette](https://dl.acm.org/doi/10.1145/2666356.2594340), written in OCaml. This is a playground for me to learn about symbolic execution and symbolic virtual machines.

## Features and TODOs

- [x] Solvable types
  - [x] Intrinsic typing via GADTs
  - [x] Booleans
    - [x] Simple partial evaluation
    - [ ] Full partial evaluation with a normal form and a mini-SAT solver?
  - [x] Integers
    - [x] Simple partial evaluation
    - [ ] Full partial evaluation with a normal form?
  - [ ] Bitvectors
  - [ ] Uninterpreted sorts and functions
    - How to type this?
- [ ] Unsolvable types
  - [x] Naive union (i.e., `'a union = (Solvable.bool * 'a) list`): [lib/union.ml](./lib/union.ml)
    - [ ] Mutually exclusive guard
    - [ ] Consistency check (assert at least one guard is true)
  - [x] Tree-based union and merging a la [Grisette](https://github.com/lsrcz/grisette): [lib/unionG.ml](./lib/unionG.ml)
    - [x] Merging algorithm
    - [x] Composable merging strategies for primitives, products, and sums (via partial profunctor?!)
  - [ ] Trie-based union and merging: [lib/unionP.ml](./lib/unionP.ml)
    - Does this help at all?
    - How to handle sums?
    - How to handle user-defined ADTs?
  - [ ] Memoization
  - [ ] Merging a la Rosette
    - This is probably not possible since we don't have a dynamically typed language with introspection
  - [ ] Lifted structs and sums
    - How to implement and type these without introspection (Rosette) and type classes (Grisette)?
- [x] Virtual machine
  - [x] Basic APIs:
    - [x] `assert`, `if`
    - [ ] user `assume` a la [Rosette 4](https://unsat.cs.washington.edu/papers/porncharoenwase-leanette.pdf)
    - [x] `bool*`, `int*`
    - [x] `solve`
    - [x] `optimize`
    - [ ] `verify`
    - [ ] CEGIS-style `synthesize`
  - [x] Effect-handler based implementation
  - [ ] Monadic implementation