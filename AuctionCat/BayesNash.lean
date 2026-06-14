import AuctionCat.SecondPrice
import AuctionCat.FirstPrice
import AuctionCat.Vickrey3

/-!
# AuctionCat.BayesNash

Bayes-Nash equilibrium for the two-bidder Vickrey auction.

A strategy profile `(s₁, s₂)` is a *Bayes-Nash equilibrium* iff
neither bidder can increase their expected utility (over the prior
on the opponent's type) by unilaterally deviating to some other
strategy.

For Vickrey specifically, truthful bidding is even stronger than
Bayes-Nash: it is a (weakly) dominant strategy — it weakly
dominates every deviation at every realised valuation profile.
This is the `vickrey_truthful_dominant` theorem already proved in
`AuctionCat.SecondPrice`.

This file lifts that pointwise dominance to expected utilities, by
showing that a pointwise utility inequality survives summation
under a prior with nonnegative weights.  The Bayes-Nash claim for
the symmetric-truthful profile then follows immediately.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Pointwise inequality on a `Fin`-indexed family lifts to
    inequality on the `Fin.sumRat`. -/
private theorem Fin.sumRat_le {n : Nat} {f g : Fin n → Rat}
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

/-- Bidder 1's expected utility in a 2-bidder Vickrey auction with
    bidder 1 using strategy `s1`, bidder 2 using strategy `s2`,
    valuation `v1`, and prior `p` on bidder 2's valuation. -/
def vickreyExpectedUtility (n : Nat) (s1 s2 : Fin n → Fin n)
    (v1 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    p v2 * ((vickreyUtility n v1 (s1 v1) (s2 v2)).val : Nat).cast)

/-- Strategy `s1` is a *best response* to `s2` at every type, given
    prior `p`, in the 2-bidder Vickrey auction. -/
def IsBestResponseVickrey (n : Nat) (s1 s2 : Fin n → Fin n)
    (p : Fin n → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    vickreyExpectedUtility n s1 s2 v1 p
    ≥ vickreyExpectedUtility n s1' s2 v1 p

/-- A pair of strategies `(s1, s2)` is a *Bayes-Nash equilibrium*
    in the 2-bidder Vickrey auction under prior `p`. -/
def IsBayesNashVickrey (n : Nat) (s1 s2 : Fin n → Fin n)
    (p : Fin n → Rat) : Prop :=
  IsBestResponseVickrey n s1 s2 p
  ∧ IsBestResponseVickrey n s2 s1 p

/-- Truthful bidding is a best response to any opposing strategy
    in Vickrey, against any prior with nonnegative weights. -/
theorem vickrey_truthful_best_response (n : Nat) (s2 : Fin n → Fin n)
    (p : Fin n → Rat) (h_nn : ∀ v, 0 ≤ p v) :
    IsBestResponseVickrey n (fun v => v) s2 p := by
  intro s1' v1
  unfold vickreyExpectedUtility
  apply Fin.sumRat_le
  intro v2
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v2)
  -- Pointwise utility dominance.
  have := vickrey_truthful_dominant n v1 (s1' v1) (s2 v2)
  -- Convert from .val ≥ .val (Nat) to .val.cast ≥ .val.cast (Rat).
  exact_mod_cast this

/-- Truthful-truthful is a Bayes-Nash equilibrium in Vickrey, for
    any prior with nonnegative weights. -/
theorem vickrey_truthful_is_bayes_nash (n : Nat) (p : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ p v) :
    IsBayesNashVickrey n (fun v => v) (fun v => v) p :=
  ⟨vickrey_truthful_best_response n (fun v => v) p h_nn,
   vickrey_truthful_best_response n (fun v => v) p h_nn⟩

/-! ## Three-bidder Vickrey Bayes-Nash -/

/-- Bidder 1's expected utility in a 3-bidder Vickrey auction with
    strategies `(s1, s2, s3)`, valuation `v1`, and joint prior `p23`
    on bidders 2's and 3's valuations (encoded as `Fin (n * n)`). -/
def vickreyExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v1 : Fin n) (p23 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v23 : Fin (n * n) =>
    p23 v23 *
      ((vickreyUtility3 n v1 (s1 v1) (s2 (Fin.first v23))
                              (s3 (Fin.second v23))).val : Nat).cast)

/-- Truthful bidding is a best response to any opposing strategies
    `(s2, s3)` in 3-bidder Vickrey, for any joint prior with
    nonnegative weights. -/
theorem vickrey3_truthful_best_response (n : Nat)
    (s1' s2 s3 : Fin n → Fin n) (p23 : Fin (n * n) → Rat)
    (h_nn : ∀ v23, 0 ≤ p23 v23) (v1 : Fin n) :
    vickreyExpectedUtility3 n (fun v => v) s2 s3 v1 p23
    ≥ vickreyExpectedUtility3 n s1' s2 s3 v1 p23 := by
  unfold vickreyExpectedUtility3
  apply Fin.sumRat_le
  intro v23
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v23)
  have := vickrey3_truthful_dominant n v1 (s1' v1)
            (s2 (Fin.first v23)) (s3 (Fin.second v23))
  exact_mod_cast this

/-- Strategy `s1` is a best response (from bidder 1's perspective) to
    `(s2, s3)` at every type, given joint prior `p23`, in 3-bidder
    Vickrey. -/
def IsBestResponseVickrey3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (p23 : Fin (n * n) → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    vickreyExpectedUtility3 n s1 s2 s3 v1 p23
    ≥ vickreyExpectedUtility3 n s1' s2 s3 v1 p23

/-- A profile `(s1, s2, s3)` is a *symmetric Bayes-Nash equilibrium*
    of the 3-bidder Vickrey auction under priors `(p23, p13, p12)`
    iff each bidder's strategy is a best response to the other two,
    measured by their own prior over the others' valuations. -/
def IsBayesNashVickrey3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (p23 p13 p12 : Fin (n * n) → Rat) : Prop :=
  IsBestResponseVickrey3 n s1 s2 s3 p23
  ∧ IsBestResponseVickrey3 n s2 s1 s3 p13
  ∧ IsBestResponseVickrey3 n s3 s1 s2 p12

/-- Truthful-truthful-truthful is a Bayes-Nash equilibrium in
    3-bidder Vickrey, for any joint priors with nonnegative weights. -/
theorem vickrey3_truthful_is_bayes_nash (n : Nat)
    (p23 p13 p12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ p23 v) (h_nn13 : ∀ v, 0 ≤ p13 v)
    (h_nn12 : ∀ v, 0 ≤ p12 v) :
    IsBayesNashVickrey3 n (fun v => v) (fun v => v) (fun v => v)
                          p23 p13 p12 :=
  ⟨fun s1' v1 => vickrey3_truthful_best_response n s1' (fun v => v)
                  (fun v => v) p23 h_nn23 v1,
   fun s2' v2 => vickrey3_truthful_best_response n s2' (fun v => v)
                  (fun v => v) p13 h_nn13 v2,
   fun s3' v3 => vickrey3_truthful_best_response n s3' (fun v => v)
                  (fun v => v) p12 h_nn12 v3⟩

/-! ## Fpsb Bayes-Nash (negative result)

  Truthful is NOT a best response, hence (truthful, truthful) is NOT
  a Bayes-Nash equilibrium of fpsb under generic priors. -/

/-- Bidder 1's expected utility in a 2-bidder fpsb auction. -/
def fpsbExpectedUtility (n : Nat) (s1 s2 : Fin n → Fin n)
    (v1 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    p v2 * ((fpsbUtility n v1 (s1 v1) (s2 v2)).val : Nat).cast)

/-- Strategy `s1` is a *best response* to `s2` at every type, given
    prior `p`, in the 2-bidder fpsb auction. -/
def IsBestResponseFpsb (n : Nat) (s1 s2 : Fin n → Fin n)
    (p : Fin n → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    fpsbExpectedUtility n s1 s2 v1 p
    ≥ fpsbExpectedUtility n s1' s2 v1 p

/-- A pair `(s1, s2)` is a *Bayes-Nash equilibrium* in the 2-bidder
    fpsb auction under prior `p`. -/
def IsBayesNashFpsb (n : Nat) (s1 s2 : Fin n → Fin n)
    (p : Fin n → Rat) : Prop :=
  IsBestResponseFpsb n s1 s2 p
  ∧ IsBestResponseFpsb n s2 s1 p

/-- **Pointwise non-dominance witness for fpsb at uniform-style prior**
    (concrete `n = 2`).  At `v1 = 1`, truthful expected utility = 0,
    while bidding `0` against the constant-zero opponent gives
    expected utility `1` (since opponent always bids `0`, b1 = 0
    wins by tiebreak and pays 0).  Hence truthful is strictly
    dominated by the zero-bid deviation under this prior. -/
theorem fpsb_truthful_strictly_dominated_n2 :
    fpsbExpectedUtility 2 (fun v => v) (fun _ => ⟨0, by decide⟩)
        ⟨1, by decide⟩ (fun v => if v.val = 0 then 1 else 0)
    < fpsbExpectedUtility 2 (fun _ => ⟨0, by decide⟩)
        (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0) := by
  unfold fpsbExpectedUtility fpsbUtility
  native_decide

/-- **fpsb truthful is NOT a best response against constant-zero
    opponent under the prior concentrated at `v = 0`** (concrete
    `n = 2`).  Direct lift of `fpsb_truthful_strictly_dominated_n2`
    via the `IsBestResponseFpsb` definition. -/
theorem fpsb_truthful_not_best_response_n2 :
    ¬ IsBestResponseFpsb 2 (fun v => v) (fun _ => ⟨0, by decide⟩)
        (fun v => if v.val = 0 then 1 else 0) := by
  intro h_br
  have h_le :=
    h_br (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
  exact absurd h_le (not_le_of_lt fpsb_truthful_strictly_dominated_n2)

/-- **(Truthful, truthful) is NOT a Bayes-Nash equilibrium of fpsb at
    n=2** under the prior concentrated at `v = 0`.  Bidder 1's
    expected truthful utility is 0 (by `fpsb_truthful_expected_utility_zero`),
    while their expected zero-bid deviation utility at `v1 = 1` is 1
    (winner pays 0 since opponent bids `0` truthfully under this
    prior).  This breaks the truthful best-response side of the BN
    conjunction. -/
theorem fpsb_truthful_truthful_not_bayes_nash_n2 :
    ¬ IsBayesNashFpsb 2 (fun v => v) (fun v => v)
        (fun v => if v.val = 0 then 1 else 0) := by
  intro h_bn
  have h_br1 := h_bn.1
  have h_le :=
    h_br1 (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
  rw [fpsb_truthful_expected_utility_zero] at h_le
  have h_rhs :
      fpsbExpectedUtility 2 (fun _ : Fin 2 => ⟨0, by decide⟩)
        (fun v : Fin 2 => v) ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0) = 1 := by
    unfold fpsbExpectedUtility fpsbUtility
    native_decide
  rw [h_rhs] at h_le
  exact absurd h_le (by norm_num)

/-- Pointwise utility of truthful bidder 1 in fpsb is always zero:
    if `b1 = v` then either the bidder loses (utility = 0) or wins
    and pays own bid = own valuation (utility = `v - v = 0`). -/
theorem fpsb_utility_truthful_val_eq_zero (n : Nat) (v b2 : Fin n) :
    (fpsbUtility n v v b2).val = 0 := by
  unfold fpsbUtility
  by_cases h : v.val ≥ b2.val
  · simp [h]
  · simp [h]

/-- **Truthful expected utility in fpsb is zero under any prior and
    against any opponent strategy**.  Direct lift of the pointwise
    `fpsb_utility_truthful_val_eq_zero` via linearity of `Fin.sumRat`. -/
theorem fpsb_truthful_expected_utility_zero (n : Nat) (s2 : Fin n → Fin n)
    (v1 : Fin n) (p : Fin n → Rat) :
    fpsbExpectedUtility n (fun v => v) s2 v1 p = 0 := by
  unfold fpsbExpectedUtility
  have h : ∀ v2 : Fin n,
      p v2 * ((fpsbUtility n v1 v1 (s2 v2)).val : Nat).cast = 0 := by
    intro v2
    rw [fpsb_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 1's expected utility in a 3-bidder fpsb auction. -/
def fpsbExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v1 : Fin n) (p23 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v23 : Fin (n * n) =>
    p23 v23 *
      ((fpsbUtility3 n v1 (s1 v1) (s2 (Fin.first v23))
                          (s3 (Fin.second v23))).val : Nat).cast)

/-- **Truthful expected utility in 3-bidder fpsb is zero under any
    joint prior and against any opponent strategies**.  Same zero-
    surplus observation as the 2-bidder case. -/
theorem fpsb3_truthful_expected_utility_zero (n : Nat)
    (s2 s3 : Fin n → Fin n) (v1 : Fin n) (p23 : Fin (n * n) → Rat) :
    fpsbExpectedUtility3 n (fun v => v) s2 s3 v1 p23 = 0 := by
  unfold fpsbExpectedUtility3
  have h : ∀ v23 : Fin (n * n),
      p23 v23 * ((fpsbUtility3 n v1 v1 (s2 (Fin.first v23))
                                       (s3 (Fin.second v23))).val
                : Nat).cast = 0 := by
    intro v23
    rw [fpsb3_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Strategy `s1` is a *best response* (from bidder 1's perspective)
    to `(s2, s3)` at every type, given joint prior `p23`, in 3-bidder
    fpsb. -/
def IsBestResponseFpsb3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (p23 : Fin (n * n) → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    fpsbExpectedUtility3 n s1 s2 s3 v1 p23
    ≥ fpsbExpectedUtility3 n s1' s2 s3 v1 p23

/-- A profile `(s1, s2, s3)` is a *Bayes-Nash equilibrium* of the
    3-bidder fpsb auction under priors `(p23, p13, p12)`. -/
def IsBayesNashFpsb3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (p23 p13 p12 : Fin (n * n) → Rat) : Prop :=
  IsBestResponseFpsb3 n s1 s2 s3 p23
  ∧ IsBestResponseFpsb3 n s2 s1 s3 p13
  ∧ IsBestResponseFpsb3 n s3 s1 s2 p12

/-- **Strict-dominance witness for 3-bidder fpsb truthful at n=2**.
    At `v1 = 1`, bidding 0 against constant-zero opponents gives
    expected utility 1, while truthful gives 0. -/
theorem fpsb3_truthful_strictly_dominated_n2 :
    fpsbExpectedUtility3 2 (fun v => v) (fun _ => ⟨0, by decide⟩)
        (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0)
    < fpsbExpectedUtility3 2 (fun _ => ⟨0, by decide⟩)
        (fun _ => ⟨0, by decide⟩) (fun _ => ⟨0, by decide⟩)
        ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0) := by
  unfold fpsbExpectedUtility3 fpsbUtility3
  native_decide

/-- **3-bidder fpsb truthful is NOT a best response** against
    constant-zero opponents under a prior concentrated at v=0
    (concrete n=2). -/
theorem fpsb3_truthful_not_best_response_n2 :
    ¬ IsBestResponseFpsb3 2 (fun v => v) (fun _ => ⟨0, by decide⟩)
        (fun _ => ⟨0, by decide⟩)
        (fun v => if v.val = 0 then 1 else 0) := by
  intro h_br
  have h_le :=
    h_br (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
  exact absurd h_le (not_le_of_lt fpsb3_truthful_strictly_dominated_n2)

/-- **(Truthful, truthful, truthful) is NOT a Bayes-Nash equilibrium
    of 3-bidder fpsb at n=2** under the joint prior concentrated at
    `(v2, v3) = (0, 0)`.  Same idea as the 2-bidder case: bidder 1's
    expected truthful utility is 0, while bidding 0 at v1=1 wins by
    tiebreak against the (concentrated) opponents and yields utility
    1.  This breaks the bidder-1 best-response side of the BN
    conjunction. -/
theorem fpsb3_truthful_truthful_truthful_not_bayes_nash_n2 :
    ¬ IsBayesNashFpsb3 2 (fun v => v) (fun v => v) (fun v => v)
        (fun v => if v.val = 0 then 1 else 0)
        (fun v => if v.val = 0 then 1 else 0)
        (fun v => if v.val = 0 then 1 else 0) := by
  intro h_bn
  have h_br1 := h_bn.1
  have h_le :=
    h_br1 (fun _ => ⟨0, by decide⟩) ⟨1, by decide⟩
  rw [fpsb3_truthful_expected_utility_zero] at h_le
  have h_rhs :
      fpsbExpectedUtility3 2 (fun _ : Fin 2 => ⟨0, by decide⟩)
        (fun v : Fin 2 => v) (fun v : Fin 2 => v) ⟨1, by decide⟩
        (fun v => if v.val = 0 then 1 else 0) = 1 := by
    unfold fpsbExpectedUtility3 fpsbUtility3
    native_decide
  rw [h_rhs] at h_le
  exact absurd h_le (by norm_num)

/-- Bidder 1's expected utility in a 2-bidder fpsb-with-reserve
    auction. -/
def fpsbReserveExpectedUtility (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (v1 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    p v2 * ((fpsbReserveUtility n r v1 (s1 v1) (s2 v2)).val : Nat).cast)

/-- **Truthful expected utility in fpsb-with-reserve is zero under any
    reserve, prior, and opponent strategy** (2 bidders). -/
theorem fpsbReserve_truthful_expected_utility_zero (n : Nat) (r : Fin n)
    (s2 : Fin n → Fin n) (v1 : Fin n) (p : Fin n → Rat) :
    fpsbReserveExpectedUtility n r (fun v => v) s2 v1 p = 0 := by
  unfold fpsbReserveExpectedUtility
  have h : ∀ v2 : Fin n,
      p v2 * ((fpsbReserveUtility n r v1 v1 (s2 v2)).val : Nat).cast = 0 := by
    intro v2
    rw [fpsbReserve_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Strategy `s1` is a *best response* to `s2` in the 2-bidder fpsb-
    with-reserve auction at reserve `r` and prior `p`. -/
def IsBestResponseFpsbReserve (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    fpsbReserveExpectedUtility n r s1 s2 v1 p
    ≥ fpsbReserveExpectedUtility n r s1' s2 v1 p

/-- A pair `(s1, s2)` is a *Bayes-Nash equilibrium* in the 2-bidder
    fpsbReserve auction at reserve `r` under prior `p`. -/
def IsBayesNashFpsbReserve (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) : Prop :=
  IsBestResponseFpsbReserve n r s1 s2 p
  ∧ IsBestResponseFpsbReserve n r s2 s1 p

/-- **Expected utility is zero for any strategy at maximal reserve**
    (2 bidders).  Direct lift of `fpsbReserve_utility_max_reserve_val_eq_zero`
    to expected utility. -/
theorem fpsbReserve_expected_utility_max_reserve_zero (n : Nat) (hn : 0 < n)
    (s1 s2 : Fin n → Fin n) (v1 : Fin n) (p : Fin n → Rat) :
    fpsbReserveExpectedUtility n ⟨n - 1, by omega⟩ s1 s2 v1 p = 0 := by
  unfold fpsbReserveExpectedUtility
  have h : ∀ v2 : Fin n,
      p v2 * ((fpsbReserveUtility n ⟨n - 1, by omega⟩ v1 (s1 v1) (s2 v2)).val
              : Nat).cast = 0 := by
    intro v2
    rw [fpsbReserve_utility_max_reserve_val_eq_zero n hn]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- **At maximal reserve, every strategy is trivially a best response
    in fpsbReserve**.  Since every strategy yields zero expected
    utility, no deviation can do better. -/
theorem fpsbReserve_any_strategy_best_response_at_max_reserve (n : Nat)
    (hn : 0 < n) (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) :
    IsBestResponseFpsbReserve n ⟨n - 1, by omega⟩ s1 s2 p := by
  intro s1' v1
  rw [fpsbReserve_expected_utility_max_reserve_zero n hn,
      fpsbReserve_expected_utility_max_reserve_zero n hn]
  exact Rat.le_refl

/-- **Trivial Bayes-Nash at maximal reserve**: at `r = n - 1`,
    `(s1, s2)` is a Bayes-Nash equilibrium for ANY strategies and
    prior, since every strategy yields zero expected utility. -/
theorem fpsbReserve_any_pair_is_bayes_nash_at_max_reserve (n : Nat)
    (hn : 0 < n) (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) :
    IsBayesNashFpsbReserve n ⟨n - 1, by omega⟩ s1 s2 p :=
  ⟨fpsbReserve_any_strategy_best_response_at_max_reserve n hn s1 s2 p,
   fpsbReserve_any_strategy_best_response_at_max_reserve n hn s2 s1 p⟩

/-- Bidder 1's expected utility in a 3-bidder fpsb-with-reserve
    auction. -/
def fpsbReserveExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v1 : Fin n)
    (p23 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v23 : Fin (n * n) =>
    p23 v23 *
      ((fpsbReserveUtility3 n r v1 (s1 v1) (s2 (Fin.first v23))
                                     (s3 (Fin.second v23))).val
       : Nat).cast)

/-- **Truthful expected utility in 3-bidder fpsb-with-reserve is zero
    under any reserve, joint prior, and opponent strategies**. -/
theorem fpsb3Reserve_truthful_expected_utility_zero (n : Nat) (r : Fin n)
    (s2 s3 : Fin n → Fin n) (v1 : Fin n) (p23 : Fin (n * n) → Rat) :
    fpsbReserveExpectedUtility3 n r (fun v => v) s2 s3 v1 p23 = 0 := by
  unfold fpsbReserveExpectedUtility3
  have h : ∀ v23 : Fin (n * n),
      p23 v23 * ((fpsbReserveUtility3 n r v1 v1 (s2 (Fin.first v23))
                                                (s3 (Fin.second v23))).val
                : Nat).cast = 0 := by
    intro v23
    rw [fpsb3Reserve_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 2's expected utility in a 2-bidder fpsb auction.  Mirrors
    `fpsbExpectedUtility` for bidder 2's perspective. -/
def fpsbBidder2ExpectedUtility (n : Nat) (s1 s2 : Fin n → Fin n)
    (v2 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v1 : Fin n =>
    p v1 * ((fpsbBidder2Util n v2 (s1 v1) (s2 v2)).val : Nat).cast)

/-- **Bidder 2's truthful expected utility in fpsb is zero under any
    prior and opponent strategy** (2 bidders). -/
theorem fpsb_bidder2_truthful_expected_utility_zero (n : Nat)
    (s1 : Fin n → Fin n) (v2 : Fin n) (p : Fin n → Rat) :
    fpsbBidder2ExpectedUtility n s1 (fun v => v) v2 p = 0 := by
  unfold fpsbBidder2ExpectedUtility
  have h : ∀ v1 : Fin n,
      p v1 * ((fpsbBidder2Util n v2 (s1 v1) v2).val : Nat).cast = 0 := by
    intro v1
    rw [fpsb_bidder2_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 2's expected utility in a 2-bidder fpsb-with-reserve
    auction. -/
def fpsbReserveBidder2ExpectedUtility (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (v2 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v1 : Fin n =>
    p v1 * ((fpsbReserveBidder2Util n r v2 (s1 v1) (s2 v2)).val
              : Nat).cast)

/-- **Bidder 2's truthful expected utility in fpsbReserve is zero
    under any prior, opponent strategy, and reserve** (2 bidders). -/
theorem fpsbReserve_bidder2_truthful_expected_utility_zero (n : Nat)
    (r : Fin n) (s1 : Fin n → Fin n) (v2 : Fin n) (p : Fin n → Rat) :
    fpsbReserveBidder2ExpectedUtility n r s1 (fun v => v) v2 p = 0 := by
  unfold fpsbReserveBidder2ExpectedUtility
  have h : ∀ v1 : Fin n,
      p v1 * ((fpsbReserveBidder2Util n r v2 (s1 v1) v2).val
              : Nat).cast = 0 := by
    intro v1
    rw [fpsbReserve_bidder2_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 2's expected utility in a 3-bidder fpsb auction. -/
def fpsbBidder2ExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v2 : Fin n) (p13 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v13 : Fin (n * n) =>
    p13 v13 *
      ((fpsbBidder2Util3 n v2 (s1 (Fin.first v13)) (s2 v2)
                              (s3 (Fin.second v13))).val
       : Nat).cast)

/-- **Bidder 2's truthful expected utility in 3-bidder fpsb is zero
    under any joint prior and opponent strategies**. -/
theorem fpsb3_bidder2_truthful_expected_utility_zero (n : Nat)
    (s1 s3 : Fin n → Fin n) (v2 : Fin n) (p13 : Fin (n * n) → Rat) :
    fpsbBidder2ExpectedUtility3 n s1 (fun v => v) s3 v2 p13 = 0 := by
  unfold fpsbBidder2ExpectedUtility3
  have h : ∀ v13 : Fin (n * n),
      p13 v13 * ((fpsbBidder2Util3 n v2 (s1 (Fin.first v13)) v2
                                          (s3 (Fin.second v13))).val
                : Nat).cast = 0 := by
    intro v13
    rw [fpsb3_bidder2_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 3's expected utility in a 3-bidder fpsb auction. -/
def fpsbBidder3ExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v3 : Fin n) (p12 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v12 : Fin (n * n) =>
    p12 v12 *
      ((fpsbBidder3Util3 n v3 (s1 (Fin.first v12))
                              (s2 (Fin.second v12)) (s3 v3)).val
       : Nat).cast)

/-- **Bidder 3's truthful expected utility in 3-bidder fpsb is zero
    under any joint prior and opponent strategies**. -/
theorem fpsb3_bidder3_truthful_expected_utility_zero (n : Nat)
    (s1 s2 : Fin n → Fin n) (v3 : Fin n) (p12 : Fin (n * n) → Rat) :
    fpsbBidder3ExpectedUtility3 n s1 s2 (fun v => v) v3 p12 = 0 := by
  unfold fpsbBidder3ExpectedUtility3
  have h : ∀ v12 : Fin (n * n),
      p12 v12 * ((fpsbBidder3Util3 n v3 (s1 (Fin.first v12))
                                          (s2 (Fin.second v12)) v3).val
                : Nat).cast = 0 := by
    intro v12
    rw [fpsb3_bidder3_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 2's expected utility in a 3-bidder fpsbReserve auction. -/
def fpsbReserveBidder2ExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v2 : Fin n)
    (p13 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v13 : Fin (n * n) =>
    p13 v13 *
      ((fpsbReserveBidder2Util3 n r v2 (s1 (Fin.first v13)) (s2 v2)
                                        (s3 (Fin.second v13))).val
       : Nat).cast)

/-- **Bidder 2's truthful expected utility in 3-bidder fpsbReserve is
    zero under any reserve, joint prior, and opponent strategies**. -/
theorem fpsb3Reserve_bidder2_truthful_expected_utility_zero (n : Nat)
    (r : Fin n) (s1 s3 : Fin n → Fin n) (v2 : Fin n)
    (p13 : Fin (n * n) → Rat) :
    fpsbReserveBidder2ExpectedUtility3 n r s1 (fun v => v) s3 v2 p13 = 0 := by
  unfold fpsbReserveBidder2ExpectedUtility3
  have h : ∀ v13 : Fin (n * n),
      p13 v13 * ((fpsbReserveBidder2Util3 n r v2 (s1 (Fin.first v13)) v2
                                                  (s3 (Fin.second v13))).val
                : Nat).cast = 0 := by
    intro v13
    rw [fpsb3Reserve_bidder2_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-- Bidder 3's expected utility in a 3-bidder fpsbReserve auction. -/
def fpsbReserveBidder3ExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v3 : Fin n)
    (p12 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v12 : Fin (n * n) =>
    p12 v12 *
      ((fpsbReserveBidder3Util3 n r v3 (s1 (Fin.first v12))
                                        (s2 (Fin.second v12)) (s3 v3)).val
       : Nat).cast)

/-- **Bidder 3's truthful expected utility in 3-bidder fpsbReserve is
    zero under any reserve, joint prior, and opponent strategies**. -/
theorem fpsb3Reserve_bidder3_truthful_expected_utility_zero (n : Nat)
    (r : Fin n) (s1 s2 : Fin n → Fin n) (v3 : Fin n)
    (p12 : Fin (n * n) → Rat) :
    fpsbReserveBidder3ExpectedUtility3 n r s1 s2 (fun v => v) v3 p12 = 0 := by
  unfold fpsbReserveBidder3ExpectedUtility3
  have h : ∀ v12 : Fin (n * n),
      p12 v12 * ((fpsbReserveBidder3Util3 n r v3 (s1 (Fin.first v12))
                                                  (s2 (Fin.second v12)) v3).val
                : Nat).cast = 0 := by
    intro v12
    rw [fpsb3Reserve_bidder3_utility_truthful_val_eq_zero]
    simp
  rw [Fin.sumRat_congr h]
  exact Fin.sumRat_const_zero

/-! ## Spsb vs fpsb pointwise utility comparison

  Under truthful play, Vickrey utility weakly dominates fpsb utility
  at every joint-bid input: spsb's `v - b2 = v - opponent's bid` is
  always ≥ fpsb's identically-zero `v - v` (when winner). -/

/-- Pointwise: vickreyUtility under truthful play weakly dominates
    fpsbUtility under truthful play at every joint-bid input. -/
theorem vickreyUtility_truthful_ge_fpsbUtility_truthful (n : Nat)
    (v b2 : Fin n) :
    (vickreyUtility n v v b2).val ≥ (fpsbUtility n v v b2).val := by
  rw [fpsb_utility_truthful_val_eq_zero]
  exact Nat.zero_le _

/-- **Expected**: vickreyExpectedUtility under truthful play weakly
    dominates fpsbExpectedUtility under truthful play for any
    nonneg prior and opponent strategy.  RHS is zero by
    `fpsb_truthful_expected_utility_zero`, LHS is nonneg by
    nonnegativity of vickrey utility values and prior weights. -/
theorem vickreyExpectedUtility_truthful_ge_fpsbExpectedUtility_truthful
    (n : Nat) (s2 : Fin n → Fin n) (v1 : Fin n) (p : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ p v) :
    vickreyExpectedUtility n (fun v => v) s2 v1 p
    ≥ fpsbExpectedUtility n (fun v => v) s2 v1 p := by
  rw [fpsb_truthful_expected_utility_zero]
  unfold vickreyExpectedUtility
  apply Fin.sumRat_le
  intro v2
  have h_cast_nn : (0 : Rat)
      ≤ ((vickreyUtility n v1 v1 (s2 v2)).val : Nat).cast := by
    exact_mod_cast Nat.zero_le _
  calc (0 : Rat)
      = 0 * ((vickreyUtility n v1 v1 (s2 v2)).val : Nat).cast := by
        rw [Rat.zero_mul]
    _ ≤ p v2 * ((vickreyUtility n v1 v1 (s2 v2)).val : Nat).cast :=
        Rat.mul_le_mul_of_nonneg_right (h_nn v2) h_cast_nn

/-- Pointwise (3 bidders): vickreyUtility3 under truthful play weakly
    dominates fpsbUtility3 under truthful play. -/
theorem vickreyUtility3_truthful_ge_fpsbUtility3_truthful (n : Nat)
    (v b2 b3 : Fin n) :
    (vickreyUtility3 n v v b2 b3).val ≥ (fpsbUtility3 n v v b2 b3).val := by
  rw [fpsb3_utility_truthful_val_eq_zero]
  exact Nat.zero_le _

/-- **Expected (3 bidders)**: vickreyExpectedUtility3 under truthful
    play weakly dominates fpsbExpectedUtility3 under truthful play
    for any nonneg joint prior and opponent strategies. -/
theorem vickreyExpectedUtility3_truthful_ge_fpsbExpectedUtility3_truthful
    (n : Nat) (s2 s3 : Fin n → Fin n) (v1 : Fin n)
    (p23 : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ p23 v) :
    vickreyExpectedUtility3 n (fun v => v) s2 s3 v1 p23
    ≥ fpsbExpectedUtility3 n (fun v => v) s2 s3 v1 p23 := by
  rw [fpsb3_truthful_expected_utility_zero]
  unfold vickreyExpectedUtility3
  apply Fin.sumRat_le
  intro v23
  have h_cast_nn : (0 : Rat)
      ≤ ((vickreyUtility3 n v1 v1 (s2 (Fin.first v23))
                                   (s3 (Fin.second v23))).val
         : Nat).cast := by
    exact_mod_cast Nat.zero_le _
  calc (0 : Rat)
      = 0 * ((vickreyUtility3 n v1 v1 (s2 (Fin.first v23))
                                       (s3 (Fin.second v23))).val
            : Nat).cast := by rw [Rat.zero_mul]
    _ ≤ p23 v23
        * ((vickreyUtility3 n v1 v1 (s2 (Fin.first v23))
                                     (s3 (Fin.second v23))).val
          : Nat).cast :=
        Rat.mul_le_mul_of_nonneg_right (h_nn v23) h_cast_nn


end AuctionCat
