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
    bidding.  Both expected revenues = 5/9. -/
example :
    IsRevenueEquivalent 3
      (biddedMechanism 3 (halfShading 3) (halfShading 3)
        (firstPriceSealedBid 3))
      (secondPriceSealedBid 3)
      (uniformPrior 3) := by
  unfold IsRevenueEquivalent
  native_decide

/-- Negative example at n = 2: discrete half-shading collapses
    (1/2 = 0), so every fpsb-half-shaded outcome ties at bid 0 and
    bidder 1 always wins paying 0.  Expected fpsb revenue = 0, but
    spsb truthful expected revenue = 1/4 (the diagonal entry (1, 1)
    contributes 1; weighted by 1/4 prior).  These differ. -/
example :
    ¬ IsRevenueEquivalent 2
      (biddedMechanism 2 (halfShading 2) (halfShading 2)
        (firstPriceSealedBid 2))
      (secondPriceSealedBid 2)
      (uniformPrior 2) := by
  unfold IsRevenueEquivalent
  native_decide

/-- Negative example at n = 4: half-shading maps (0, 1, 2, 3) to
    (0, 0, 1, 1), creating asymmetric stepping.  Expected fpsb
    revenue = 3/4, expected spsb revenue = 7/8.  These differ —
    a parity mismatch between the discrete grid and the continuous
    half-shading equilibrium. -/
example :
    ¬ IsRevenueEquivalent 4
      (biddedMechanism 4 (halfShading 4) (halfShading 4)
        (firstPriceSealedBid 4))
      (secondPriceSealedBid 4)
      (uniformPrior 4) := by
  unfold IsRevenueEquivalent
  native_decide

/-- Positive example at n = 5: half-shading maps (0, 1, 2, 3, 4) to
    (0, 0, 1, 1, 2), and both expected revenues compute to 6/5. -/
example :
    IsRevenueEquivalent 5
      (biddedMechanism 5 (halfShading 5) (halfShading 5)
        (firstPriceSealedBid 5))
      (secondPriceSealedBid 5)
      (uniformPrior 5) := by
  unfold IsRevenueEquivalent
  native_decide

end AuctionCat
