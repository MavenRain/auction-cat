import AuctionCat.Auction
import AuctionCat.Revenue
import AuctionCat.Revenue3
import AuctionCat.ExpectedRevenueComparison
import AuctionCat.BayesNashPipeline
import AuctionCat.Envelope

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

/-! ## Strategic-equivalence revenue examples

  The strategic equivalences English ≅ SPSB and Dutch ≅ FPSB lift
  trivially to revenue equivalence at every concrete `n` and prior.
  Each example invokes the rfl-level corollary directly. -/

/-- English ≅ SPSB revenue equivalence at `n = 3` under uniform
    prior — direct application of `english_is_revenue_equivalent_spsb`. -/
example :
    IsRevenueEquivalent 3 (englishAuction 3) (secondPriceSealedBid 3)
                          (uniformPrior 3) :=
  english_is_revenue_equivalent_spsb 3 (uniformPrior 3)

/-- Dutch ≅ FPSB revenue equivalence at `n = 3` under uniform prior
    — direct application of `dutch_is_revenue_equivalent_fpsb`. -/
example :
    IsRevenueEquivalent 3 (dutchAuction 3) (firstPriceSealedBid 3)
                          (uniformPrior 3) :=
  dutch_is_revenue_equivalent_fpsb 3 (uniformPrior 3)

/-- **Four-way revenue equivalence at `n = 3`**: chaining
    half-shaded FPSB ≡ SPSB (RET-style) ≡ English (kernel rfl)
    gives that half-shaded Dutch's substitute (half-shaded FPSB) has
    the same revenue as English under uniform prior. -/
example :
    IsRevenueEquivalent 3
      (biddedMechanism 3 (halfShading 3) (halfShading 3)
        (firstPriceSealedBid 3))
      (englishAuction 3)
      (uniformPrior 3) := by
  unfold IsRevenueEquivalent
  native_decide

/-! ## Concrete expected-revenue values under truthful play

  Numeric verification of the closed-form expected-revenue
  expressions at small `n` under uniform prior. -/

/-- At `n = 2` uniform prior: E[fpsb truthful] = 3/4. -/
example :
    expectedRevenue 2 (firstPriceSealedBid 2) (uniformPrior 2) = 3 / 4 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 2` uniform prior: E[spsb truthful] = 1/4. -/
example :
    expectedRevenue 2 (secondPriceSealedBid 2) (uniformPrior 2) = 1 / 4 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 3` uniform prior: E[fpsb truthful] = 13/9. -/
example :
    expectedRevenue 3 (firstPriceSealedBid 3) (uniformPrior 3) = 13 / 9 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 3` uniform prior: E[spsb truthful] = 5/9.  Recorded
    redundantly here for use in the gap example below. -/
example :
    expectedRevenue 3 (secondPriceSealedBid 3) (uniformPrior 3) = 5 / 9 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- **Expected-revenue gap at `n = 3`**: under uniform prior,
    truthful fpsb's expected revenue exceeds truthful spsb's by
    `13/9 - 5/9 = 8/9`.  This is the discrete IPV revenue gap. -/
example :
    expectedRevenue 3 (firstPriceSealedBid 3) (uniformPrior 3)
    - expectedRevenue 3 (secondPriceSealedBid 3) (uniformPrior 3)
    = 8 / 9 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-! ## Three-bidder concrete expected-revenue values

  Same pattern at three bidders.  The 2-bidder uniform spsb gives
  1/4 and fpsb gives 3/4 (n=2); the 3-bidder uniform spsb gives 1/2
  and fpsb gives 7/8 (n=2), already in Revenue3.lean. -/

/-- **Three-bidder expected-revenue gap at `n = 2`**: under uniform
    prior over 8 valuation triples, truthful fpsb3's expected
    revenue exceeds truthful spsb3's by `7/8 - 1/2 = 3/8`. -/
example :
    expectedRevenue3 2 (firstPriceSealedBid3 2) (uniformPrior3 2)
    - expectedRevenue3 2 (secondPriceSealedBid3 2) (uniformPrior3 2)
    = 3 / 8 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- vickrey bidder-1 truthful expected utility at `n = 3` uniform
    prior `1/3`, `v1 = 2` is nonneg. -/
example :
    0 ≤ vickreyExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) := by
  apply vickreyExpectedUtility_truthful_nonneg
  intro _
  native_decide

/-- vickrey3 bidder-1 truthful expected utility at `n = 3` uniform
    joint prior `1/9`, `v1 = 2` is nonneg. -/
example :
    0 ≤ vickreyExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  apply vickreyExpectedUtility3_truthful_nonneg
  intro _
  native_decide

/-- vickrey bidder-2 strict-positive utility witness at `n = 3`
    uniform prior `1/3`, `v2 = 2`: value = `(2 + 1 + 0)/3 = 1 > 0`. -/
example :
    0 < vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) := by
  have h : vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 1 := by
    unfold vickreyBidder2ExpectedUtility vickreyBidder2Util
    native_decide
  rw [h]
  decide

/-- vickrey3 bidder-3 strict-positive utility witness at `n = 3`
    uniform joint prior `1/9`, `v3 = 2`: bidder 3 wins only when
    both opponents bid strictly below 2.  The four winning profiles
    (0,0), (1,0), (0,1), (1,1) contribute v - max(opp_b1, opp_b2) =
    2, 1, 1, 1 (total 5), giving expected utility `5/9 > 0`. -/
example :
    0 < vickreyBidder3ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  have h : vickreyBidder3ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 5 / 9 := by
    unfold vickreyBidder3ExpectedUtility3 vickreyBidder3Util3
    native_decide
  rw [h]
  native_decide

/-- vickrey3 bidder-2 strict-positive utility witness at `n = 3`
    uniform joint prior `1/9`, `v2 = 2`: bidder 2 wins iff opp_b1 < 2
    AND 2 ≥ opp_b3 (weak — bidder 2 has priority over 3); pays
    max(opp_b1, opp_b3) on win.  Expected utility = `5/9 > 0`. -/
example :
    0 < vickreyBidder2ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  have h : vickreyBidder2ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 5 / 9 := by
    unfold vickreyBidder2ExpectedUtility3 vickreyBidder2Util3
    native_decide
  rw [h]
  native_decide

/-- **Concrete fpsb3 truthful = 0** at `n = 3`, uniform joint prior
    `1/9`, `v1 = 2`. -/
example :
    fpsbExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 0 :=
  fpsb3_truthful_expected_utility_zero 3 (fun v => v) (fun v => v)
    ⟨2, by decide⟩ (fun _ => (1/9 : Rat))

/-- **Strict bidder-1 vickrey3 > fpsb3 gap** at `n = 3`, uniform 1/9,
    `v1 = 2`: `5/9 > 0`. -/
example :
    fpsbExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat))
    < vickreyExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  have h_fpsb : fpsbExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 0 :=
    fpsb3_truthful_expected_utility_zero 3 (fun v => v) (fun v => v)
      ⟨2, by decide⟩ (fun _ => (1/9 : Rat))
  have h_vk : vickreyExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 5 / 9 := by
    unfold vickreyExpectedUtility3 vickreyUtility3
    native_decide
  rw [h_fpsb, h_vk]
  native_decide

/-- **Strict bidder-1 vickrey > fpsb gap** at `n = 3`, uniform 1/3,
    `v1 = 2`: `1 > 0`. -/
example :
    fpsbExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
        (fun _ => (1/3 : Rat))
    < vickreyExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
        (fun _ => (1/3 : Rat)) := by
  have h_fpsb : fpsbExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 0 :=
    fpsb_truthful_expected_utility_zero 3 (fun v => v) ⟨2, by decide⟩
      (fun _ => (1/3 : Rat))
  have h_vk : vickreyExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 1 := by
    unfold vickreyExpectedUtility vickreyUtility
    native_decide
  rw [h_fpsb, h_vk]
  native_decide

/-- **Strict bidder-2 vickrey > fpsb gap** at `n = 3`, uniform 1/3,
    `v2 = 2`: `1 > 0`. -/
example :
    fpsbBidder2ExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
        (fun _ => (1/3 : Rat))
    < vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) := by
  have h_fpsb : fpsbBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 0 :=
    fpsb_bidder2_truthful_expected_utility_zero 3 (fun v => v)
      ⟨2, by decide⟩ (fun _ => (1/3 : Rat))
  have h_vk : vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 1 := by
    unfold vickreyBidder2ExpectedUtility vickreyBidder2Util
    native_decide
  rw [h_fpsb, h_vk]
  native_decide

/-- **Weak vickrey ≥ fpsb comparison via the theorem** at `n = 3`,
    uniform prior `1/3`, `v1 = 2` (bidder 1). -/
example :
    vickreyExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
        (fun _ => (1/3 : Rat))
    ≥ fpsbExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
        (fun _ => (1/3 : Rat)) := by
  apply vickreyExpectedUtility_truthful_ge_fpsbExpectedUtility_truthful
  intro _
  native_decide

/-- **Weak vickrey3 ≥ fpsb3 comparison via the theorem** at `n = 3`,
    uniform joint prior `1/9`, `v1 = 2` (bidder 1). -/
example :
    vickreyExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat))
    ≥ fpsbExpectedUtility3 3 (fun v => v) (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  apply vickreyExpectedUtility3_truthful_ge_fpsbExpectedUtility3_truthful
  intro _
  native_decide

/-- **Pipeline-level spsbAuction ≥ fpsbAuction via the dominance
    theorem** at `n = 3`, uniform prior `1/3`, `v1 = 2`. -/
example :
    auctionExpectedBidder1Util 3 (spsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util 3 (fpsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder1Util_spsbAuction_ge_fpsbAuction
  intro _
  native_decide

/-- **Pipeline-level spsb3Auction ≥ fpsb3Auction via the dominance
    theorem** at `n = 3`, uniform joint prior `1/9`, `v1 = 2`. -/
example :
    auctionExpectedBidder1Util3 3 (spsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util3 3 (fpsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder1Util3_spsb3Auction_ge_fpsb3Auction
  intro _
  native_decide

/-- **Pipeline-level spsbReserveAuction ≥ fpsbReserveAuction** at
    `n = 3`, `r = 1`, uniform prior `1/3`, `v1 = 2`. -/
example :
    auctionExpectedBidder1Util 3 (spsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util 3 (fpsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder1Util_spsbReserveAuction_ge_fpsbReserveAuction
  intro _
  native_decide

/-- **Pipeline-level spsb3ReserveAuction ≥ fpsb3ReserveAuction** at
    `n = 3`, `r = 1`, uniform joint prior `1/9`, `v1 = 2`. -/
example :
    auctionExpectedBidder1Util3 3 (spsb3ReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util3 3 (fpsb3ReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder1Util3_spsb3ReserveAuction_ge_fpsb3ReserveAuction
  intro _
  native_decide

/-- **Bidder-2 pipeline-level spsbAuction ≥ fpsbAuction** at `n = 3`,
    uniform prior `1/3`, `v2 = 2`. -/
example :
    auctionExpectedBidder2Util 3 (spsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder2Util 3 (fpsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder2Util_spsbAuction_ge_fpsbAuction
  intro _
  native_decide

/-- **Bidder-3 pipeline-level spsb3Auction ≥ fpsb3Auction** at
    `n = 3`, uniform joint prior `1/9`, `v3 = 2`. -/
example :
    auctionExpectedBidder3Util3 3 (spsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder3Util3 3 (fpsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder3Util3_spsb3Auction_ge_fpsb3Auction
  intro _
  native_decide

/-- **4-way pipeline dominance bundle via main summary** at `n = 3`,
    `r = 1`, uniform priors.  Extracts all four bidder-1 dominance
    inequalities from one application of
    `spsb_ge_fpsb_pipeline_main`. -/
example :
    auctionExpectedBidder1Util 3 (spsbAuction 3)
        (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
      ≥ auctionExpectedBidder1Util 3 (fpsbAuction 3)
        (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ∧ auctionExpectedBidder1Util 3 (spsbReserveAuction 3 ⟨1, by decide⟩)
        (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
      ≥ auctionExpectedBidder1Util 3 (fpsbReserveAuction 3 ⟨1, by decide⟩)
        (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ∧ auctionExpectedBidder1Util3 3 (spsb3Auction 3)
        (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
      ≥ auctionExpectedBidder1Util3 3 (fpsb3Auction 3)
        (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
    ∧ auctionExpectedBidder1Util3 3 (spsb3ReserveAuction 3 ⟨1, by decide⟩)
        (fun _ => (1/9 : Rat)) ⟨2, by decide⟩
      ≥ auctionExpectedBidder1Util3 3 (fpsb3ReserveAuction 3 ⟨1, by decide⟩)
        (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ := by
  apply spsb_ge_fpsb_pipeline_main
  · intro _; native_decide
  · intro _; native_decide

/-- **Bidder-2 pipeline-level spsbReserveAuction ≥ fpsbReserveAuction**
    at `n = 3`, `r = 1`, uniform prior `1/3`, `v2 = 2`. -/
example :
    auctionExpectedBidder2Util 3 (spsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder2Util 3 (fpsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ := by
  apply auctionExpectedBidder2Util_spsbReserveAuction_ge_fpsbReserveAuction
  intro _
  native_decide

/-- **Bidder-1 vickrey truthful val nonneg via the bundle** at
    concrete arbitrary inputs.  Direct projection of the first
    component of `vickrey_truthful_val_nonneg_main`. -/
example (v b2 : Fin 3) :
    0 ≤ (vickreyUtility 3 v v b2).val :=
  (vickrey_truthful_val_nonneg_main 3 v b2 ⟨0, by decide⟩ ⟨0, by decide⟩).1

/-- **Concrete vickrey expected utility at n=2** uniform prior `1/2`,
    `v1 = 1` evaluates to `1/2`. -/
example :
    vickreyExpectedUtility 2 (fun v => v) (fun v => v) ⟨1, by decide⟩
        (fun _ => (1/2 : Rat)) = 1 / 2 := by
  unfold vickreyExpectedUtility vickreyUtility
  native_decide

end AuctionCat
