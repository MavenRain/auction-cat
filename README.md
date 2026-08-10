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

- [x] `MarkovCat` typeclass + `FinStoch` instance
- [x] `OpenGamesCat` open game / equilibrium / monoidal product
- [x] `AuctionCat` first-price, second-price, Dutch ≅ FirstPrice iso,
      second-price truthfulness
- [x] Revenue equivalence proved through the discrete envelope theorem
      (`Envelope.lean`: `vickrey_envelope`, `revenue_equivalence`)
- [x] Optimal reserve price: prove that `r = 1` maximizes seller expected
      revenue at binary valuations, for both formats, with two and three
      bidders
- [ ] Entry fees: add a participation-fee mechanism, its revenue
      accounting, and the discrete revenue-equivalence analogue with fees
- [ ] Risk aversion: add a concave bidder utility and prove the
      first-price ≥ second-price revenue comparison at binary valuations
- [ ] First-price equilibrium, general case: extend the `n = 2` negative
      Bayes-Nash result and analyze the half-shading candidate strategy
      (see the gap note in `KernelFirstPrice.lean`)
- [x] Reserve-format outcome equivalence at `n = 2`, `r = 1`:
      `spsbReserveFn 2 ⟨1⟩ = fpsbReserveFn 2 ⟨1⟩`, with the revenue
      coincidence as a corollary
- [ ] Cleanup: shared `highestBid3` / `secondHighest3` helpers across
      `Revenue.lean` and `Revenue3.lean`

Completion marker: when each box above shows a check, the Chapter 2 IPV
formalization is complete.  At that point, replace this paragraph with
"**v1.0: Chapter 2 IPV scope complete**" and report completion.

## Building

```sh
lake update
lake build
```

Lean toolchain is pinned to `v4.30.0-rc1` to match `kan-tactics` and
`comp-cat-theory`.

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
