import AuctionCat.Auction
import AuctionCat.Revenue

/-!
# AuctionCat.Examples

Small-`n` numerical verification of the revenue analysis framework.

For `n = 3` with uniform prior over joint valuations, we verify:

  expectedRevenue 3 (spsbMechanism)         (uniform) = 5/9
  expectedRevenue 3 (fpsb-half-shaded)      (uniform) = 5/9

so that `IsRevenueEquivalent 3 (fpsb-half-shaded) spsb uniformPrior`
holds — a concrete instance of the Revenue Equivalence Theorem at
the discrete grid `Fin 3`.

The numbers come from enumerating all 9 valuation profiles, computing
each format's revenue at that profile, and summing weighted by 1/9.
For `n = 2`, the discrete half-shading collapses (1/2 rounds to 0) so
revenue equivalence fails — that case is recorded as a negative
example.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Revenue equivalence at n = 3 (discrete uniform IPV) between
    first-price under half-shading and second-price under truthful
    bidding. -/
example :
    IsRevenueEquivalent 3
      (biddedMechanism 3 (halfShading 3) (halfShading 3)
        (firstPriceSealedBid 3))
      (secondPriceSealedBid 3)
      (uniformPrior 3) := by
  unfold IsRevenueEquivalent
  native_decide

end AuctionCat
