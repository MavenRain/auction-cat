import AuctionCat.Auction
import AuctionCat.Revenue
import AuctionCat.Revenue3
import AuctionCat.ExpectedRevenueComparison
import AuctionCat.BayesNashPipeline

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

/-- Three-bidder dominance verified at `n = 2`: fpsb3 truthful
    expected revenue ≥ spsb3 truthful expected revenue under uniform
    prior.  Direct application of `expectedRevenue3_fpsb3_ge_spsb3`. -/
example :
    expectedRevenue3 2 (firstPriceSealedBid3 2) (uniformPrior3 2)
    ≥ expectedRevenue3 2 (secondPriceSealedBid3 2) (uniformPrior3 2) :=
  expectedRevenue3_fpsb3_ge_spsb3 2 (uniformPrior3 2)
    (fun _ => by unfold uniformPrior3; native_decide)

/-! ## Dominance instantiations at concrete n (2 bidders)

  Direct applications of `expectedRevenue_fpsb_ge_spsb` to small
  uniform priors.  Each example produces a `Rat`-level inequality
  witness. -/

/-- Two-bidder dominance verified at `n = 3`: fpsb truthful expected
    revenue ≥ spsb truthful expected revenue under uniform prior. -/
example :
    expectedRevenue 3 (firstPriceSealedBid 3) (uniformPrior 3)
    ≥ expectedRevenue 3 (secondPriceSealedBid 3) (uniformPrior 3) :=
  expectedRevenue_fpsb_ge_spsb 3 (uniformPrior 3)
    (fun _ => by unfold uniformPrior; native_decide)

/-- Dutch ≥ English under uniform prior at `n = 3` — strategic
    equivalence corollary of the fpsb-spsb dominance. -/
example :
    expectedRevenue 3 (dutchAuction 3) (uniformPrior 3)
    ≥ expectedRevenue 3 (englishAuction 3) (uniformPrior 3) :=
  expectedRevenue_dutch_ge_english 3 (uniformPrior 3)
    (fun _ => by unfold uniformPrior; native_decide)

/-- Three-bidder Dutch ≥ English under uniform prior at `n = 2`. -/
example :
    expectedRevenue3 2 (dutchAuction3 2) (uniformPrior3 2)
    ≥ expectedRevenue3 2 (englishAuction3 2) (uniformPrior3 2) :=
  expectedRevenue3_dutch3_ge_english3 2 (uniformPrior3 2)
    (fun _ => by unfold uniformPrior3; native_decide)

/-! ## Reserve-auction concrete expected-revenue values

  Numeric verification of the reserve closed forms at small `n`
  under uniform prior, showing how a binding reserve increases
  spsb revenue toward fpsb. -/

/-- At `n = 2`, `r = 1` uniform prior: E[fpsbReserve] = 3/4 (same as
    no-reserve since the only excluded profile (0,0) had revenue 0). -/
example :
    expectedRevenue 2 (fpsbReserve 2 ⟨1, by decide⟩) (uniformPrior 2)
    = 3 / 4 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 2`, `r = 1` uniform prior: E[spsbReserve] = 3/4 (jumps
    from no-reserve's 1/4 — a binding reserve closes the revenue gap
    with fpsb). -/
example :
    expectedRevenue 2 (spsbReserve 2 ⟨1, by decide⟩) (uniformPrior 2)
    = 3 / 4 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 2`, `r = 1`: with this binding reserve, fpsbReserve and
    spsbReserve yield equal expected revenue — the reserve eliminates
    the truthful-play revenue gap. -/
example :
    IsRevenueEquivalent 2 (fpsbReserve 2 ⟨1, by decide⟩)
                          (spsbReserve 2 ⟨1, by decide⟩)
                          (uniformPrior 2) := by
  unfold IsRevenueEquivalent expectedRevenue uniformPrior
  native_decide

/-- At `n = 3`, `r = 1` uniform prior: E[spsbReserve] = 1 (jumps
    from no-reserve's 5/9). -/
example :
    expectedRevenue 3 (spsbReserve 3 ⟨1, by decide⟩) (uniformPrior 3)
    = 1 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 3`, `r = 2` (maximal reserve) uniform prior:
    E[fpsbReserve] = E[spsbReserve] = 10/9.  Winner always pays exactly
    r when allocation occurs, so both formats collapse to the same
    revenue. -/
example :
    expectedRevenue 3 (fpsbReserve 3 ⟨2, by decide⟩) (uniformPrior 3)
    = 10 / 9 := by
  unfold expectedRevenue uniformPrior
  native_decide

example :
    expectedRevenue 3 (spsbReserve 3 ⟨2, by decide⟩) (uniformPrior 3)
    = 10 / 9 := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `n = 3`, `r = n - 1 = 2`: revenue-equivalence witness via the
    structural `fpsbReserve_max_is_revenue_equivalent_spsbReserve_max`
    theorem (no recomputation needed). -/
example :
    IsRevenueEquivalent 3 (fpsbReserve 3 ⟨3 - 1, by decide⟩)
                          (spsbReserve 3 ⟨3 - 1, by decide⟩)
                          (uniformPrior 3) :=
  fpsbReserve_max_is_revenue_equivalent_spsbReserve_max 3 (by decide)
    (uniformPrior 3)

/-! ## Three-bidder reserve numeric examples -/

/-- At `n = 2` (3 bidders), `r = 1 = n - 1` uniform prior:
    E[fpsb3Reserve] = 7/8 (every profile with at least one bid ≥ 1
    contributes — 7 of 8 profiles, revenue 1 each). -/
example :
    expectedRevenue3 2 (fpsb3Reserve 2 ⟨1, by decide⟩) (uniformPrior3 2)
    = 7 / 8 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- At `n = 2` (3 bidders), `r = 1 = n - 1`: E[spsb3Reserve] = 7/8
    (matches fpsb3Reserve at maximal reserve, jumps from no-reserve's
    1/2). -/
example :
    expectedRevenue3 2 (spsb3Reserve 2 ⟨1, by decide⟩) (uniformPrior3 2)
    = 7 / 8 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- At `n = 2` (3 bidders), maximal reserve: structural revenue
    equivalence via `fpsb3Reserve_max_is_revenue_equivalent_spsb3Reserve_max`. -/
example :
    IsRevenueEquivalent3 2 (fpsb3Reserve 2 ⟨2 - 1, by decide⟩)
                            (spsb3Reserve 2 ⟨2 - 1, by decide⟩)
                            (uniformPrior3 2) :=
  fpsb3Reserve_max_is_revenue_equivalent_spsb3Reserve_max 2 (by decide)
    (uniformPrior3 2)

/-! ## Pipeline-level spsb ≥ fpsb utility witnesses

  Direct applications of the pipeline dominance theorems at small
  uniform-ish priors, exercising the structural theorems at
  concrete `n` and `v1`. -/

/-- At `n = 3`, uniform-style prior `1/3`, `v1 = 2`: spsb pipeline
    utility weakly dominates fpsb pipeline utility. -/
example :
    auctionExpectedBidder1Util 3 (spsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util 3 (fpsbAuction 3)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ :=
  auctionExpectedBidder1Util_spsbAuction_ge_fpsbAuction 3
    (fun _ => (1/3 : Rat))
    (fun _ => by norm_num) ⟨2, by decide⟩

/-- At `n = 3`, `r = 1`, `v1 = 2`: spsbReserve pipeline utility
    weakly dominates fpsbReserve pipeline utility under uniform-style
    prior `1/3`. -/
example :
    auctionExpectedBidder1Util 3 (spsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩
    ≥ auctionExpectedBidder1Util 3 (fpsbReserveAuction 3 ⟨1, by decide⟩)
      (fun _ => (1/3 : Rat)) ⟨2, by decide⟩ :=
  auctionExpectedBidder1Util_spsbReserveAuction_ge_fpsbReserveAuction
    3 ⟨1, by decide⟩ (fun _ => (1/3 : Rat))
    (fun _ => by norm_num) ⟨2, by decide⟩

/-- **Concrete numeric witness of the spsb > fpsb pipeline gap** at
    `n = 2`, uniform prior `1/2`, `v1 = 1`: spsb pipeline yields
    `1/2` (winner pays opponent's bid 0 with prob 1/2, util = 1; tie
    pays own bid 1 with util 0).  Fpsb pipeline yields `0`.  Strict
    gap of `1/2`. -/
example :
    auctionExpectedBidder1Util 2 (spsbAuction 2)
      (fun _ => (1/2 : Rat)) ⟨1, by decide⟩ = 1 / 2 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq]
  unfold vickreyExpectedUtility vickreyUtility
  native_decide

example :
    auctionExpectedBidder1Util 2 (fpsbAuction 2)
      (fun _ => (1/2 : Rat)) ⟨1, by decide⟩ = 0 :=
  auctionExpectedBidder1Util_fpsbAuction_eq_zero 2 (fun _ => (1/2 : Rat))
    ⟨1, by decide⟩

/-- **3-bidder concrete strict gap** at `n = 3`, uniform joint
    prior `1/9`, `v1 = 2`: spsb3 pipeline yields `5/9`; fpsb3
    pipeline yields `0`.  Strict gap of `5/9`. -/
example :
    auctionExpectedBidder1Util3 3 (spsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ = 5 / 9 := by
  rw [auctionExpectedBidder1Util3_spsb3Auction_eq]
  unfold vickreyExpectedUtility3 vickreyUtility3
  native_decide

example :
    auctionExpectedBidder1Util3 3 (fpsb3Auction 3)
      (fun _ => (1/9 : Rat)) ⟨2, by decide⟩ = 0 :=
  auctionExpectedBidder1Util3_fpsb3Auction_eq_zero 3
    (fun _ => (1/9 : Rat)) ⟨2, by decide⟩

/-- **Kernel-level strict-gap numeric witness** at `n = 3`, uniform
    prior `1/3`, `v1 = 2`: kernel-level vickreyExpectedUtility yields
    `1` (the integer-valued sum collapses by the uniform-1/3
    weighting), while fpsbExpectedUtility yields `0`. -/
example :
    vickreyExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
      (fun _ => (1/3 : Rat)) = 1 := by
  unfold vickreyExpectedUtility vickreyUtility
  native_decide

example :
    fpsbExpectedUtility 3 (fun v => v) (fun v => v) ⟨2, by decide⟩
      (fun _ => (1/3 : Rat)) = 0 :=
  fpsb_truthful_expected_utility_zero 3 (fun v => v) ⟨2, by decide⟩
    (fun _ => (1/3 : Rat))

/-- **Trivial Bayes-Nash at maximal reserve**: at `n = 3`, `r = 2`
    (maximal), any strategy pair is a Bayes-Nash equilibrium of
    fpsbReserve under any prior — every strategy yields zero
    utility. -/
example (s1 s2 : Fin 3 → Fin 3) (p : Fin 3 → Rat) :
    IsBayesNashFpsbReserve 3 ⟨3 - 1, by decide⟩ s1 s2 p :=
  fpsbReserve_any_pair_is_bayes_nash_at_max_reserve 3 (by decide) s1 s2 p

/-- **Trivial Bayes-Nash at maximal reserve (3 bidders)**: at `n = 2`,
    `r = 1` (maximal), any strategy triple is a Bayes-Nash
    equilibrium of fpsb3Reserve under any joint priors. -/
example (s1 s2 s3 : Fin 2 → Fin 2) (p23 p13 p12 : Fin (2 * 2) → Rat) :
    IsBayesNashFpsb3Reserve 2 ⟨2 - 1, by decide⟩ s1 s2 s3 p23 p13 p12 :=
  fpsb3Reserve_any_triple_is_bayes_nash_at_max_reserve 2 (by decide)
    s1 s2 s3 p23 p13 p12

/-- **Concrete strict-positivity** of spsb truthful expected utility
    at `n = 3`, uniform prior `1/3`, `v1 = 2`.  Vickrey gives bidder 1
    a positive expected surplus, in contrast to fpsb's identically
    zero. -/
example :
    0 < vickreyExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) := by
  have h : vickreyExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 1 := by
    unfold vickreyExpectedUtility vickreyUtility
    native_decide
  rw [h]
  norm_num

/-- **fpsb (truthful, truthful) is not BN at n=3** under prior
    concentrated at `v=0`.  Same structure as the n=2 case. -/
example :
    ¬ IsBayesNashFpsb 3 (fun v => v) (fun v => v)
        (fun v => if v.val = 0 then 1 else 0) := by
  intro h_bn
  have h_br1 := h_bn.1
  have h_le :=
    h_br1 (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
  rw [fpsb_truthful_expected_utility_zero] at h_le
  have h_rhs :
      fpsbExpectedUtility 3 (fun _ : Fin 3 => ⟨0, by decide⟩)
        (fun v : Fin 3 => v) ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0) = 1 := by
    unfold fpsbExpectedUtility fpsbUtility
    native_decide
  rw [h_rhs] at h_le
  exact absurd h_le (by norm_num)

/-- **Bidder-2 strict-positivity** for vickrey at `n = 3`, uniform
    prior `1/3`, `v2 = 2`: vickreyBidder2ExpectedUtility = 1 > 0.
    By symmetry across bidders, top valuation yields positive
    expected surplus from either bidder's perspective in Vickrey. -/
example :
    0 < vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) := by
  have h : vickreyBidder2ExpectedUtility 3 (fun v => v) (fun v => v)
        ⟨2, by decide⟩ (fun _ => (1/3 : Rat)) = 1 := by
    unfold vickreyBidder2ExpectedUtility vickreyBidder2Util
    native_decide
  rw [h]
  norm_num

/-- **3-bidder bidder-3 strict-positivity** for vickrey3 at `n = 3`,
    uniform joint prior `1/9`, `v3 = 2`: vickreyBidder3ExpectedUtility3
    > 0.  Bidder 3 with top valuation gets positive expected surplus
    in the 3-bidder Vickrey auction. -/
example :
    0 < vickreyBidder3ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) := by
  have h : vickreyBidder3ExpectedUtility3 3 (fun v => v) (fun v => v)
        (fun v => v) ⟨2, by decide⟩ (fun _ => (1/9 : Rat)) = 1 / 3 := by
    unfold vickreyBidder3ExpectedUtility3 vickreyBidder3Util3
    native_decide
  rw [h]
  norm_num

/-! ## Reserve monotonicity (spsb at n=3 uniform)

  At `n = 3` under uniform prior, raising the reserve from 0 to
  1 to 2 strictly increases spsb expected revenue: 5/9 < 1 < 10/9.
  This is the discrete-IPV illustration of the seller's incentive
  to raise reserves (subject to the standard cap from the
  distributional support). -/

/-- spsb revenue at `r = 0` is at most spsb revenue at `r = 1`
    (n=3 uniform): 5/9 ≤ 1. -/
example :
    expectedRevenue 3 (spsbReserve 3 ⟨0, by decide⟩) (uniformPrior 3)
    ≤ expectedRevenue 3 (spsbReserve 3 ⟨1, by decide⟩) (uniformPrior 3) := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- spsb revenue at `r = 1` is at most spsb revenue at `r = 2`
    (n=3 uniform): 1 ≤ 10/9. -/
example :
    expectedRevenue 3 (spsbReserve 3 ⟨1, by decide⟩) (uniformPrior 3)
    ≤ expectedRevenue 3 (spsbReserve 3 ⟨2, by decide⟩) (uniformPrior 3) := by
  unfold expectedRevenue uniformPrior
  native_decide

/-! ## Reserve non-monotonicity (fpsb at n=3 uniform)

  In contrast to spsb, fpsb revenue is NOT monotonic in the reserve
  at n=3.  Raising `r = 1 → 2` strictly DECREASES revenue (13/9 →
  10/9) because the reserve excludes profiles that would otherwise
  contribute positively (max=1 profiles now extract 0 instead of 1).
  This is the standard auction-theory observation that fpsb's revenue
  is at most as monotone as spsb's in the reserve. -/

/-- fpsbReserve revenue at `r = 2` is strictly less than at `r = 0`
    (n=3 uniform): 10/9 < 13/9. -/
example :
    expectedRevenue 3 (fpsbReserve 3 ⟨2, by decide⟩) (uniformPrior 3)
    < expectedRevenue 3 (fpsbReserve 3 ⟨0, by decide⟩) (uniformPrior 3) := by
  unfold expectedRevenue uniformPrior
  native_decide

/-- At `r = 1`, fpsbReserve revenue equals at `r = 0` (n=3 uniform):
    both give 13/9.  Reserve `r = 1` excludes only the (0, 0)
    profile which contributed 0 already. -/
example :
    expectedRevenue 3 (fpsbReserve 3 ⟨1, by decide⟩) (uniformPrior 3)
    = expectedRevenue 3 (fpsbReserve 3 ⟨0, by decide⟩) (uniformPrior 3) := by
  unfold expectedRevenue uniformPrior
  native_decide

end AuctionCat
