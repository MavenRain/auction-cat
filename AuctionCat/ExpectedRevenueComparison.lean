import AuctionCat.Revenue
import AuctionCat.Revenue3

/-!
# AuctionCat.ExpectedRevenueComparison

Lifting pointwise revenue comparisons to expected revenue under any
nonnegative prior.

The kernel-level pointwise inequalities

  `fpsb_revenue_ge_spsb` (2-bidder)
  `fpsb3_revenue_ge_spsb3` (3-bidder)

state that first-price extracts at least as much revenue as
second-price at every joint-bid input.  Under any prior with
nonnegative weights, summing the pointwise inequality preserves it,
giving the expected-revenue inequality.

This is the discrete IPV analogue of the standard result that under
truthful (non-equilibrium) play, fpsb extracts strictly higher
expected revenue than spsb whenever there is any chance the top two
bids differ.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Pointwise inequality on a `Fin`-indexed family lifts to inequality
    on `Fin.sumRat`.  Local re-declaration to avoid an upstream-import
    dependency on `BayesNash`. -/
private theorem Fin.sumRat_le_rev {n : Nat} {f g : Fin n → Rat}
    (h : ∀ i, f i ≤ g i) : Fin.sumRat f ≤ Fin.sumRat g := by
  induction n with
  | zero =>
    rw [Fin.sumRat_zero, Fin.sumRat_zero]
    exact Rat.le_refl
  | succ k ih =>
    rw [Fin.sumRat_succ, Fin.sumRat_succ]
    calc f 0 + Fin.sumRat (fun i => f i.succ)
        ≤ g 0 + Fin.sumRat (fun i => f i.succ) :=
          Rat.add_le_add_right.mpr (h 0)
      _ ≤ g 0 + Fin.sumRat (fun i => g i.succ) :=
          Rat.add_le_add_left.mpr (ih (fun i => h i.succ))

/-- For a deterministic mechanism `detMatrix φ`, the inner sum
    collapses by the Kronecker selector identity, giving a closed
    form for expected revenue at the bidder layer. -/
private theorem expectedRevenue_detMatrix_eq (n : Nat)
    (φ : Fin (n * n) → Fin ((2 * n) * (2 * n)))
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (detMatrix φ) prior
    = Fin.sumRat (fun v : Fin (n * n) =>
        prior v * (outcomeRevenue n (φ v) : Nat).cast) := by
  unfold expectedRevenue
  apply Fin.sumRat_congr
  intro v
  simp only [detMatrix_entry]
  rw [sumRat_kron_mul (φ v) (fun o => (outcomeRevenue n o : Nat).cast)]

/-- Three-bidder version of `expectedRevenue_detMatrix_eq`. -/
private theorem expectedRevenue3_detMatrix_eq (n : Nat)
    (φ : Fin ((n * n) * n) → Fin (((2 * n) * (2 * n)) * (2 * n)))
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (detMatrix φ) prior
    = Fin.sumRat (fun v : Fin ((n * n) * n) =>
        prior v * (outcomeRevenue3 n (φ v) : Nat).cast) := by
  unfold expectedRevenue3
  apply Fin.sumRat_congr
  intro v
  simp only [detMatrix_entry]
  rw [sumRat_kron_mul (φ v) (fun o => (outcomeRevenue3 n o : Nat).cast)]

/-- **Expected-revenue dominance** of first-price over second-price
    (2 bidders).  For any prior with nonnegative weights, fpsb's
    expected revenue is at least spsb's. -/
theorem expectedRevenue_fpsb_ge_spsb (n : Nat)
    (prior : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue n (firstPriceSealedBid n) prior
    ≥ expectedRevenue n (secondPriceSealedBid n) prior := by
  unfold firstPriceSealedBid secondPriceSealedBid
  rw [expectedRevenue_detMatrix_eq, expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_le_rev
  intro v
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v)
  exact_mod_cast fpsb_revenue_ge_spsb n v

/-- **Expected-revenue dominance** of first-price over second-price
    (3 bidders).  For any prior with nonnegative weights, fpsb3's
    expected revenue is at least spsb3's. -/
theorem expectedRevenue3_fpsb3_ge_spsb3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue3 n (firstPriceSealedBid3 n) prior
    ≥ expectedRevenue3 n (secondPriceSealedBid3 n) prior := by
  unfold firstPriceSealedBid3 secondPriceSealedBid3
  rw [expectedRevenue3_detMatrix_eq, expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_le_rev
  intro v
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v)
  exact_mod_cast fpsb3_revenue_ge_spsb3 n v

/-! ## Strategic-equivalence dominance corollaries

  Dutch ≅ FPSB and English ≅ SPSB at the mechanism level, so the
  expected-revenue inequality transports directly to:

    Dutch  ≥  English  (2 bidders)
    Dutch3 ≥ English3  (3 bidders)

  under any nonnegative prior. -/

/-- Expected-revenue dominance of Dutch over English (2 bidders) under
    truthful play and any nonnegative prior — corollary of
    `expectedRevenue_fpsb_ge_spsb` via the kernel-level strategic
    equivalences. -/
theorem expectedRevenue_dutch_ge_english (n : Nat)
    (prior : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue n (dutchAuction n) prior
    ≥ expectedRevenue n (englishAuction n) prior :=
  expectedRevenue_fpsb_ge_spsb n prior h_nn

/-- Expected-revenue dominance of Dutch over English (3 bidders) under
    truthful play and any nonnegative prior — corollary of
    `expectedRevenue3_fpsb3_ge_spsb3` via the kernel-level strategic
    equivalences. -/
theorem expectedRevenue3_dutch3_ge_english3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue3 n (dutchAuction3 n) prior
    ≥ expectedRevenue3 n (englishAuction3 n) prior :=
  expectedRevenue3_fpsb3_ge_spsb3 n prior h_nn

/-! ## Closed-form expected revenue under truthful play

  Combining the kernel-collapsing lemma `expectedRevenue_detMatrix_eq`
  with the pointwise closed forms gives clean formulas for the
  expected revenue of fpsb / spsb under any prior. -/

/-- Closed-form expected fpsb revenue under truthful play:
    `Σ_v prior(v) · max(b1, b2)`. -/
theorem expectedRevenue_fpsb_eq_sum_max (n : Nat)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (firstPriceSealedBid n) prior
    = Fin.sumRat (fun v : Fin (n * n) =>
        prior v
        * (max (Fin.first v).val (Fin.second v).val : Nat).cast) := by
  unfold firstPriceSealedBid
  rw [expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsb_revenue_eq_max]

/-- Closed-form expected spsb revenue under truthful play:
    `Σ_v prior(v) · min(b1, b2)`. -/
theorem expectedRevenue_spsb_eq_sum_min (n : Nat)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (secondPriceSealedBid n) prior
    = Fin.sumRat (fun v : Fin (n * n) =>
        prior v
        * (min (Fin.first v).val (Fin.second v).val : Nat).cast) := by
  unfold secondPriceSealedBid
  rw [expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsb_revenue_eq_min]

/-- Closed-form expected fpsb3 revenue under truthful play:
    `Σ_v prior(v) · max3(b1, b2, b3)`. -/
theorem expectedRevenue3_fpsb3_eq_sum_max (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (firstPriceSealedBid3 n) prior
    = Fin.sumRat (fun v : Fin ((n * n) * n) =>
        prior v
        * (max (Fin.first (Fin.first v)).val
            (max (Fin.second (Fin.first v)).val
                 (Fin.second v).val) : Nat).cast) := by
  unfold firstPriceSealedBid3
  rw [expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsb3_revenue_eq_max]

/-- Closed-form expected spsb3 revenue under truthful play:
    `Σ_v prior(v) · second_max3(b1, b2, b3)`. -/
theorem expectedRevenue3_spsb3_eq_sum_second_max (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (secondPriceSealedBid3 n) prior
    = Fin.sumRat (fun v : Fin ((n * n) * n) =>
        prior v
        * (max (min (Fin.first (Fin.first v)).val
                    (Fin.second (Fin.first v)).val)
              (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
                   (min (Fin.second (Fin.first v)).val
                        (Fin.second v).val)) : Nat).cast) := by
  unfold secondPriceSealedBid3
  rw [expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsb3_revenue_eq_second_max]

end AuctionCat
