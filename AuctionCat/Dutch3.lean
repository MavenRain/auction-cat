import AuctionCat.FirstPrice3
import AuctionCat.Auction

/-!
# AuctionCat.Dutch3

The Dutch (descending) auction for three bidders.

Strategically equivalent to a three-bidder first-price sealed-bid
auction: each bidder's optimal strategy is a single threshold
price (the acceptance point of the descending clock), the highest
threshold wins, and the winner pays their own threshold.

In the open-game representation, this strategic equivalence
collapses to literal kernel equality: the Dutch mechanism on
threshold-price bids is the same morphism as
`firstPriceSealedBid3`.  Same as the n = 2 case.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The Dutch (descending) auction mechanism for three bidders.
    Identical to `firstPriceSealedBid3` (strategic equivalence). -/
def dutchAuction3 (X : Nat) :
    StochasticMatrix (X * X * X) ((2 * X) * (2 * X) * (2 * X)) :=
  firstPriceSealedBid3 X

/-- Dutch auction at three bidders equals first-price-sealed-bid
    at three bidders as morphisms in `FinStoch`. -/
theorem dutch3_eq_firstPrice3 (X : Nat) :
    dutchAuction3 X = firstPriceSealedBid3 X := rfl

/-- **Dutch ≅ FPSB at the OpenGame pipeline level (3 bidders)**:
    the three-bidder Dutch auction's pipeline form equals
    `fpsb3Auction n`.  Categorical realization of the strategic
    equivalence between Dutch (descending) and first-price
    sealed-bid auctions for three bidders. -/
theorem dutch3_pipeline_eq_fpsb3Auction (n : Nat) :
    auctionScore3 n (dutchAuction3 n) = fpsb3Auction n := rfl

end AuctionCat
