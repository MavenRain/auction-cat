import AuctionCat.SecondPrice3

/-!
# AuctionCat.English3

The English (ascending) auction for three bidders.

Strategically equivalent to a three-bidder second-price sealed-bid
(Vickrey) auction: each bidder's optimal strategy is a single
dropout price (truthful dropout = bid your valuation is dominant);
the last remaining bidder wins and pays the second-to-last
bidder's dropout price.

For three bidders this is the standard Vickrey rule
"winner pays max of others' bids" implemented by
`secondPriceSealedBid3`.  The strategic equivalence collapses to
literal kernel equality.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The English (ascending) auction mechanism for three bidders.
    Identical to `secondPriceSealedBid3` (strategic equivalence). -/
def englishAuction3 (X : Nat) :
    StochasticMatrix (X * X * X) ((2 * X) * (2 * X) * (2 * X)) :=
  secondPriceSealedBid3 X

/-- English auction at three bidders equals second-price-sealed-bid
    (Vickrey) at three bidders as morphisms in `FinStoch`. -/
theorem english3_eq_secondPrice3 (X : Nat) :
    englishAuction3 X = secondPriceSealedBid3 X := rfl

end AuctionCat
