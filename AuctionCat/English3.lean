import AuctionCat.SecondPrice3
import AuctionCat.Auction

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

/-- **English ≅ SPSB at the OpenGame pipeline level (3 bidders)**:
    the three-bidder English auction's pipeline form equals
    `spsb3Auction n`.  Categorical realization of the strategic
    equivalence between English (ascending) and Vickrey
    (second-price sealed-bid) auctions for three bidders. -/
theorem english3_pipeline_eq_spsb3Auction (n : Nat) :
    auctionScore3 n (englishAuction3 n) = spsb3Auction n := rfl

end AuctionCat
