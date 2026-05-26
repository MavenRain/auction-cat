# auction-cat

A Lean 4 formalisation of Menezes and Monteiro's *An Introduction to
Auction Theory* (Oxford University Press, 2005) in the Bayesian open
games formalism, building on:

- [comp-cat-theory] for the categorical foundation (Category, Monoidal,
  SymmetricMonoidal, Optic), with each construction collapsed to a
  Kan extension.
- [kan-tactics] for proof tactics (`kan_rfl`, `kan_rw`, `kan_simp`, ...)
  each shown to be an instance of the Kan extension `kanExtend`.

[comp-cat-theory]: https://github.com/MavenRain/comp-cat-theory
[kan-tactics]: https://github.com/MavenRain/kan-tactics

## Library targets

The repository contains three Lake libraries that build on each other:

| Library | Purpose |
|---|---|
| `MarkovCat` | Markov category foundation: symmetric monoidal categories with commutative comonoid structure and total morphisms.  Hosts `FinStoch` and `BorelStoch` instances. |
| `OpenGamesCat` | Bayesian open games as morphisms in a Markov category, following Bolt-Hedges-Zahn.  Optic-based, with simultaneous play via the tensor and sequential play via composition. |
| `AuctionCat` | Menezes-Monteiro Chapter 2 (Independent Private Values): first-price sealed-bid, second-price (Vickrey), Dutch, English, reserve prices, entry fees.  Future chapters cover common values, affiliated values, mechanism design, and multiple objects. |

## Status

v0.1 in progress.  Targeted contents:

- [ ] `MarkovCat` typeclass + `FinStoch` instance
- [ ] `OpenGamesCat` open game / equilibrium / monoidal product
- [ ] `AuctionCat` first-price, second-price, Dutch ≅ FirstPrice iso,
      second-price truthfulness
- [ ] Revenue equivalence stated (proof gated on a future categorical
      envelope theorem)

## Building

```sh
lake update
lake build
```

Lean toolchain is pinned to `v4.30.0-rc1` to match `kan-tactics` and
`comp-cat-theory`.

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
