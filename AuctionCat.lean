import OpenGamesCat

/-!
# AuctionCat

Menezes and Monteiro's auction theory in the Bayesian open games
formalism.

Contents (planned for v0.3):

Chapter 2 (Independent Private Values):
- `Bidder` (open game wrapper)
- `Mechanism` (deterministic Markov morphism)
- `FirstPriceSealedBid`, `SecondPriceSealedBid`, `Dutch`, `English`
- `ReservePrice`, `EntryFee`
- Theorem: `Dutch ≅ FirstPriceSealedBid` (iso of open games)
- Theorem: dominant-strategy truthfulness of `SecondPriceSealedBid`
- `RevenueEquivalence` stated (proof gated on envelope theorem)

Currently a placeholder; built on top of `OpenGamesCat`.
-/

set_option autoImplicit false
