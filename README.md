# Camette

Symbolic virtual machine a la [Rosette](https://dl.acm.org/doi/10.1145/2666356.2594340), written in OCaml.

## Features and TODOs

- [x] Solvable types
  - [x] Intrinsic typing via GADTs
  - [x] Booleans
  - [x] Integers
  - [ ] Bitvectors
  - [ ] Uninterpreted sorts and functions
    - [ ] How to type this?
- [ ] Unsolvable types
  - [x] Naive union (i.e., `'a union = (Solvable.bool * 'a) list`)
  - [ ] Memoization
  - [ ] Merging a la Rosette
  - [ ] Tree-based union and merging a la [Grisette](https://github.com/lsrcz/grisette)
  - [ ] Lifted structs and sums
    - [ ] How to implement and type these without introspection (Rosette) and type classes (Grisette)?
- [x] Virtual machine
  - [x] Basic APIs:
    - [x] `assert`, `assume`, `if`
    - [x] `bool*`, `int*`
    - [x] `solve`
    - [x] `optimize`
    - [ ] `verify`
    - [ ] CEGIS-style `synthesize`
  - [x] Effect-handler based implementation
  - [ ] Monadic implementation