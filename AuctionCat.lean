import AuctionCat.Bidder
import AuctionCat.Mechanism

/-!
# AuctionCat

Menezes and Monteiro's auction theory in the Bayesian-open-games
formalism.

Contents:

- `AuctionCat.Bidder`     : `Bidder` type alias over `OpenGame` plus
                             smart constructor.
- `AuctionCat.Mechanism`  : `Mechanism` type alias for Markov morphisms.

Planned (Chapter 2 IPV):

- `FirstPriceSealedBid`, `SecondPriceSealedBid`, `Dutch`, `English`
- `ReservePrice`, `EntryFee`
- Theorem: `Dutch ≅ FirstPriceSealedBid` (iso of open games)
- Theorem: dominant-strategy truthfulness of `SecondPriceSealedBid`
- `RevenueEquivalence` (proof gated on envelope theorem)
-/

set_option autoImplicit false
