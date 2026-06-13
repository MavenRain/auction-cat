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

/-- **Expected-revenue dominance** of fpsbReserve over spsbReserve
    (2 bidders).  Under any prior with nonnegative weights and any
    reserve price `r`, fpsbReserve's expected revenue is at least
    spsbReserve's. -/
theorem expectedRevenue_fpsbReserve_ge_spsbReserve (n : Nat) (r : Fin n)
    (prior : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue n (fpsbReserve n r) prior
    ≥ expectedRevenue n (spsbReserve n r) prior := by
  unfold fpsbReserve spsbReserve
  rw [expectedRevenue_detMatrix_eq, expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_le_rev
  intro v
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v)
  exact_mod_cast fpsbReserve_revenue_ge_spsbReserve n r v

/-- Closed-form expected fpsbReserve revenue under truthful play:
    `Σ_v prior(v) · (if max(b1,b2) ≥ r then max(b1,b2) else 0)`. -/
theorem expectedRevenue_fpsbReserve_eq_sum (n : Nat) (r : Fin n)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (fpsbReserve n r) prior
    = Fin.sumRat (fun v : Fin (n * n) =>
        prior v
        * ((if max (Fin.first v).val (Fin.second v).val ≥ r.val
            then max (Fin.first v).val (Fin.second v).val
            else 0) : Nat).cast) := by
  unfold fpsbReserve
  rw [expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsbReserve_revenue_eq]

/-- Closed-form expected spsbReserve revenue under truthful play:
    `Σ_v prior(v) · (if max(b1,b2) ≥ r then max(r, min(b1,b2)) else 0)`. -/
theorem expectedRevenue_spsbReserve_eq_sum (n : Nat) (r : Fin n)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (spsbReserve n r) prior
    = Fin.sumRat (fun v : Fin (n * n) =>
        prior v
        * ((if max (Fin.first v).val (Fin.second v).val ≥ r.val
            then max r.val (min (Fin.first v).val (Fin.second v).val)
            else 0) : Nat).cast) := by
  unfold spsbReserve
  rw [expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsbReserve_revenue_eq]

/-- **Expected-revenue dominance** of fpsb3Reserve over spsb3Reserve
    (3 bidders).  Under any prior with nonnegative weights and any
    reserve price `r`, fpsb3Reserve's expected revenue is at least
    spsb3Reserve's. -/
theorem expectedRevenue3_fpsb3Reserve_ge_spsb3Reserve (n : Nat) (r : Fin n)
    (prior : Fin ((n * n) * n) → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    expectedRevenue3 n (fpsb3Reserve n r) prior
    ≥ expectedRevenue3 n (spsb3Reserve n r) prior := by
  unfold fpsb3Reserve spsb3Reserve
  rw [expectedRevenue3_detMatrix_eq, expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_le_rev
  intro v
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v)
  exact_mod_cast fpsb3Reserve_revenue_ge_spsb3Reserve n r v

/-- Closed-form expected fpsb3Reserve revenue under truthful play:
    `Σ_v prior(v) · (if max3 ≥ r then max3 else 0)`. -/
theorem expectedRevenue3_fpsb3Reserve_eq_sum (n : Nat) (r : Fin n)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (fpsb3Reserve n r) prior
    = Fin.sumRat (fun v : Fin ((n * n) * n) =>
        prior v
        * ((if max (Fin.first (Fin.first v)).val
                (max (Fin.second (Fin.first v)).val (Fin.second v).val)
              ≥ r.val
            then max (Fin.first (Fin.first v)).val
                  (max (Fin.second (Fin.first v)).val (Fin.second v).val)
            else 0) : Nat).cast) := by
  unfold fpsb3Reserve
  rw [expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsb3Reserve_revenue_eq]

/-- Closed-form expected spsb3Reserve revenue under truthful play:
    `Σ_v prior(v) · (if max3 ≥ r then max(r, second_max3) else 0)`. -/
theorem expectedRevenue3_spsb3Reserve_eq_sum (n : Nat) (r : Fin n)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (spsb3Reserve n r) prior
    = Fin.sumRat (fun v : Fin ((n * n) * n) =>
        prior v
        * ((if max (Fin.first (Fin.first v)).val
                (max (Fin.second (Fin.first v)).val (Fin.second v).val)
              ≥ r.val
            then max r.val
                  (max (min (Fin.first (Fin.first v)).val
                            (Fin.second (Fin.first v)).val)
                      (max (min (Fin.first (Fin.first v)).val
                                (Fin.second v).val)
                           (min (Fin.second (Fin.first v)).val
                                (Fin.second v).val)))
            else 0) : Nat).cast) := by
  unfold spsb3Reserve
  rw [expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsb3Reserve_revenue_eq]

/-! ## Expected revenue at trivial reserve = expected revenue at no reserve

  Lifting the pointwise `*Reserve_zero_revenue_eq_*` theorems to
  expected revenue under any prior. -/

/-- At reserve `r = 0`, fpsbReserve and fpsb have the same expected
    revenue under any prior. -/
theorem expectedRevenue_fpsbReserve_zero_eq_fpsb (n : Nat) (hn : 0 < n)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (fpsbReserve n ⟨0, hn⟩) prior
    = expectedRevenue n (firstPriceSealedBid n) prior := by
  unfold fpsbReserve firstPriceSealedBid
  rw [expectedRevenue_detMatrix_eq, expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsbReserve_zero_revenue_eq_fpsb]

/-- At reserve `r = 0`, spsbReserve and spsb have the same expected
    revenue under any prior. -/
theorem expectedRevenue_spsbReserve_zero_eq_spsb (n : Nat) (hn : 0 < n)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (spsbReserve n ⟨0, hn⟩) prior
    = expectedRevenue n (secondPriceSealedBid n) prior := by
  unfold spsbReserve secondPriceSealedBid
  rw [expectedRevenue_detMatrix_eq, expectedRevenue_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsbReserve_zero_revenue_eq_spsb]

/-- Three-bidder version of `expectedRevenue_fpsbReserve_zero_eq_fpsb`. -/
theorem expectedRevenue3_fpsb3Reserve_zero_eq_fpsb3 (n : Nat) (hn : 0 < n)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (fpsb3Reserve n ⟨0, hn⟩) prior
    = expectedRevenue3 n (firstPriceSealedBid3 n) prior := by
  unfold fpsb3Reserve firstPriceSealedBid3
  rw [expectedRevenue3_detMatrix_eq, expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [fpsb3Reserve_zero_revenue_eq_fpsb3]

/-- Three-bidder version of `expectedRevenue_spsbReserve_zero_eq_spsb`. -/
theorem expectedRevenue3_spsb3Reserve_zero_eq_spsb3 (n : Nat) (hn : 0 < n)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (spsb3Reserve n ⟨0, hn⟩) prior
    = expectedRevenue3 n (secondPriceSealedBid3 n) prior := by
  unfold spsb3Reserve secondPriceSealedBid3
  rw [expectedRevenue3_detMatrix_eq, expectedRevenue3_detMatrix_eq]
  apply Fin.sumRat_congr
  intro v
  rw [spsb3Reserve_zero_revenue_eq_spsb3]

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

/-! ## Expected revenue gap

  Combining `expectedRevenue_fpsb_eq_sum_max` with
  `expectedRevenue_spsb_eq_sum_min` and the pointwise gap identity
  `max = min + (max - min)`, we get the expected revenue gap
  formula: fpsb's expected revenue equals spsb's expected revenue
  plus the expected gap.  Same shape at three bidders. -/

/-- Expected revenue gap (2 bidders): fpsb truthful expected revenue
    equals spsb truthful expected revenue plus the expected pointwise
    gap `(max - min)`. -/
theorem expectedRevenue_fpsb_eq_spsb_plus_gap (n : Nat)
    (prior : Fin (n * n) → Rat) :
    expectedRevenue n (firstPriceSealedBid n) prior
    = expectedRevenue n (secondPriceSealedBid n) prior
      + Fin.sumRat (fun v : Fin (n * n) =>
          prior v
          * ((max (Fin.first v).val (Fin.second v).val
              - min (Fin.first v).val (Fin.second v).val) : Nat).cast) := by
  rw [expectedRevenue_fpsb_eq_sum_max, expectedRevenue_spsb_eq_sum_min,
      ← Fin.sumRat_add]
  apply Fin.sumRat_congr
  intro v
  have hgap : min (Fin.first v).val (Fin.second v).val
            + (max (Fin.first v).val (Fin.second v).val
              - min (Fin.first v).val (Fin.second v).val)
            = max (Fin.first v).val (Fin.second v).val := by omega
  have hcast :
      (max (Fin.first v).val (Fin.second v).val : Nat).cast
      = ((min (Fin.first v).val (Fin.second v).val : Nat).cast : Rat)
        + ((max (Fin.first v).val (Fin.second v).val
           - min (Fin.first v).val (Fin.second v).val) : Nat).cast := by
    exact_mod_cast hgap.symm
  rw [hcast, Rat.mul_add]

/-- Expected revenue gap (3 bidders): fpsb3 truthful expected revenue
    equals spsb3 truthful expected revenue plus the expected pointwise
    gap `(max3 - second_max3)`. -/
theorem expectedRevenue3_fpsb3_eq_spsb3_plus_gap (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (firstPriceSealedBid3 n) prior
    = expectedRevenue3 n (secondPriceSealedBid3 n) prior
      + Fin.sumRat (fun v : Fin ((n * n) * n) =>
          prior v
          * ((max (Fin.first (Fin.first v)).val
                  (max (Fin.second (Fin.first v)).val (Fin.second v).val)
              - max (min (Fin.first (Fin.first v)).val
                         (Fin.second (Fin.first v)).val)
                  (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
                       (min (Fin.second (Fin.first v)).val
                            (Fin.second v).val))) : Nat).cast) := by
  rw [expectedRevenue3_fpsb3_eq_sum_max,
      expectedRevenue3_spsb3_eq_sum_second_max,
      ← Fin.sumRat_add]
  apply Fin.sumRat_congr
  intro v
  have hgap :
      max (min (Fin.first (Fin.first v)).val
               (Fin.second (Fin.first v)).val)
          (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
               (min (Fin.second (Fin.first v)).val (Fin.second v).val))
      + (max (Fin.first (Fin.first v)).val
            (max (Fin.second (Fin.first v)).val (Fin.second v).val)
        - max (min (Fin.first (Fin.first v)).val
                   (Fin.second (Fin.first v)).val)
            (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
                 (min (Fin.second (Fin.first v)).val (Fin.second v).val)))
      = max (Fin.first (Fin.first v)).val
            (max (Fin.second (Fin.first v)).val (Fin.second v).val) := by
    omega
  have hcast :
      (max (Fin.first (Fin.first v)).val
            (max (Fin.second (Fin.first v)).val (Fin.second v).val)
       : Nat).cast
      = ((max (min (Fin.first (Fin.first v)).val
                   (Fin.second (Fin.first v)).val)
              (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
                   (min (Fin.second (Fin.first v)).val
                        (Fin.second v).val)) : Nat).cast : Rat)
        + ((max (Fin.first (Fin.first v)).val
                (max (Fin.second (Fin.first v)).val (Fin.second v).val)
            - max (min (Fin.first (Fin.first v)).val
                       (Fin.second (Fin.first v)).val)
                (max (min (Fin.first (Fin.first v)).val (Fin.second v).val)
                     (min (Fin.second (Fin.first v)).val
                          (Fin.second v).val))) : Nat).cast := by
    exact_mod_cast hgap.symm
  rw [hcast, Rat.mul_add]

end AuctionCat
