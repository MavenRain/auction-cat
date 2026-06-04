import AuctionCat.BayesNash

/-!
# AuctionCat.Envelope

The envelope theorem (Myerson 1981) for the two-bidder Vickrey
auction.

For a Bayes-Nash equilibrium in a Bayesian game with quasi-linear
utility, the expected payment of a type is uniquely determined by
the allocation rule (up to a normalising constant).  In the
two-bidder Vickrey setting with truthful equilibrium and prior `p`
on the opponent's valuation:

  Q(v)  := P(bidder 1 wins | v1 = v)
        = Σ_{v2 ≤ v} p(v2)

  U(v)  := E[utility | v1 = v, truthful bidding]
        = Σ_{v2 ≤ v} p(v2) * (v - v2)

  P(v)  := E[payment | v1 = v]
        = v * Q(v) - U(v)
        = Σ_{v2 ≤ v} p(v2) * v2

The discrete envelope identity reads:

  U(v) = Σ_{t < v} Q(t)

i.e., the expected utility is the sum of allocation probabilities
at lower types.  This is the discrete analogue of the continuous
envelope formula `U(v) = ∫_0^v Q(t) dt`.

This file provides the data layer for the theorem (`vickreyAllocation`,
`vickreyExpectedPayment`, `vickreyEqUtility`) and verifies the
envelope identity by `native_decide` at a small grid.  The general
proof requires `Fin.sumRat_swap` plus careful conditional algebra
and is left as a future enhancement.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder 1's expected allocation probability at type `v1` under
    Vickrey with prior `p` on bidder 2's valuation: the prior
    probability that bidder 2's valuation lies weakly below `v1`. -/
def vickreyAllocation (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    if v2.val ≤ v1.val then prior v2 else 0)

/-- Bidder 1's expected payment at type `v1` under Vickrey with
    truthful bidder 2 and prior `p`: when bidder 1 wins, the
    payment is bidder 2's valuation. -/
def vickreyExpectedPayment (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    if v2.val ≤ v1.val then prior v2 * (v2.val : Nat).cast else 0)

/-- Bidder 1's equilibrium expected utility at type `v1` under
    Vickrey with both bidders truthful and prior `p` on bidder 2. -/
def vickreyEqUtility (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    prior v2 * ((vickreyUtility n v1 v1 v2).val : Nat).cast)

/-- The right-hand side of the discrete envelope identity:
    `Σ_{t < v} Q(t)` — the cumulative allocation probability up to
    type `v - 1`. -/
def vickreyEnvelopeIntegral (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun t : Fin n =>
    if t.val < v1.val then vickreyAllocation n prior t else 0)

/-- Concrete envelope identity at `n = 4` with uniform prior `1/4`
    and `v1 = 3` (top type): both sides compute to `3/2`. -/
example :
    vickreyEqUtility 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩
    = vickreyEnvelopeIntegral 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩ := by
  unfold vickreyEqUtility vickreyEnvelopeIntegral
        vickreyAllocation
  native_decide

/-- Concrete envelope identity at `n = 5` with uniform prior `1/5`
    and `v1 = 4` (top type): both sides compute to `2`. -/
example :
    vickreyEqUtility 5 (fun _ => (1 : Rat) / 5) ⟨4, by decide⟩
    = vickreyEnvelopeIntegral 5 (fun _ => (1 : Rat) / 5) ⟨4, by decide⟩ := by
  unfold vickreyEqUtility vickreyEnvelopeIntegral
        vickreyAllocation
  native_decide

/-! ## Count helper

  The count of `t : Fin n` with `t.val < k` (for `k ≤ n`) equals
  `k` as a `Rat`.  This is the building block of the general
  envelope identity — the inner sum of the swap-form right-hand side
  is exactly such a count, weighted by the prior. -/

private theorem Fin.sumRat_count_lt : ∀ (n k : Nat), k ≤ n →
    Fin.sumRat (fun t : Fin n => if t.val < k then (1 : Rat) else 0)
    = (k : Nat).cast
  | 0, 0, _ => by rw [Fin.sumRat_zero]; rfl
  | 0, _+1, h => absurd h (by omega)
  | n+1, 0, _ => by
    rw [show (fun t : Fin (n+1) => if t.val < 0 then (1 : Rat) else 0)
          = (fun _ : Fin (n+1) => (0 : Rat))
        from funext (fun t => by
          have : ¬ (t.val < 0) := Nat.not_lt_zero _
          simp [this])]
    rw [Fin.sumRat_const_zero]
    rfl
  | n+1, k+1, h => by
    rw [Fin.sumRat_succ]
    simp
    have hk : k ≤ n := by omega
    rw [Fin.sumRat_count_lt n k hk]
    exact Rat.add_comm _ _

/-- `Fin.sumRat` of a negated family is the negation of the sum. -/
private theorem Fin.sumRat_neg : {n : Nat} → (f : Fin n → Rat) →
    Fin.sumRat (fun i => -(f i)) = -(Fin.sumRat f)
  | 0, _ => by
    rw [Fin.sumRat_zero, Fin.sumRat_zero]; rfl
  | k+1, f => by
    rw [Fin.sumRat_succ, Fin.sumRat_succ]
    rw [Fin.sumRat_neg (fun i => f i.succ)]
    rw [Rat.neg_add]

/-- `Fin.sumRat` distributes over Rat subtraction. -/
private theorem Fin.sumRat_sub {n : Nat} (f g : Fin n → Rat) :
    Fin.sumRat (fun i => f i - g i) = Fin.sumRat f - Fin.sumRat g := by
  rw [show (fun i => f i - g i) = (fun i => f i + (-(g i))) from
      funext (fun i => Rat.sub_eq_add_neg _ _)]
  rw [Fin.sumRat_add, Fin.sumRat_neg]
  exact (Rat.sub_eq_add_neg _ _).symm

/-- Cast of a Nat truncated subtraction equals Rat subtraction when
    the subtrahend is bounded by the minuend. -/
private theorem Nat.cast_sub_rat (a b : Nat) (h : a ≤ b) :
    ((b - a : Nat) : Rat) = (b : Nat).cast - (a : Nat).cast := by
  have heq : (b - a) + a = b := Nat.sub_add_cancel h
  have hcast : ((b - a : Nat) : Rat) + (a : Nat).cast = (b : Nat).cast := by
    rw [← Rat.natCast_add]; rw [heq]
  rw [← hcast]
  exact Rat.add_sub_cancel.symm

/-- The range indicator `[a ≤ t < b]` equals `[t < b] - [t < a]`
    (as Rat-valued 0/1 indicators) when `a ≤ b`. -/
private theorem indicator_range_eq_sub (a b : Nat) (h : a ≤ b) (t : Nat) :
    (if a ≤ t ∧ t < b then (1 : Rat) else 0)
    = (if t < b then (1 : Rat) else 0) - (if t < a then (1 : Rat) else 0) := by
  by_cases ha : t < a
  · have hb : t < b := Nat.lt_of_lt_of_le ha h
    have hand : ¬(a ≤ t ∧ t < b) :=
      fun ⟨hat, _⟩ => absurd hat (Nat.not_le_of_lt ha)
    rw [if_neg hand, if_pos hb, if_pos ha]
    exact Rat.sub_self.symm
  · have ha' : a ≤ t := Nat.le_of_not_lt ha
    by_cases hb : t < b
    · rw [if_pos ⟨ha', hb⟩, if_pos hb, if_neg ha]
      rw [Rat.sub_eq_add_neg]
      show 1 = 1 + (-0)
      rw [Rat.neg_zero, Rat.add_zero]
    · have hand : ¬(a ≤ t ∧ t < b) :=
        fun ⟨_, htb⟩ => absurd htb hb
      rw [if_neg hand, if_neg hb, if_neg ha]
      rw [Rat.sub_eq_add_neg]
      show 0 = 0 + (-0)
      rw [Rat.neg_zero, Rat.add_zero]

/-- The truthful Vickrey utility val collapses to the truncated Nat
    subtraction (regardless of the case split in `vickreyUtility`). -/
private theorem vickreyUtility_val_eq (n : Nat) (v b2 : Fin n) :
    (vickreyUtility n v v b2).val = v.val - b2.val := by
  unfold vickreyUtility
  by_cases h : v.val ≥ b2.val
  · rw [if_pos h]
  · rw [if_neg h]
    have hlt : v.val < b2.val := Nat.lt_of_not_le h
    have hzero : v.val - b2.val = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    exact hzero.symm

/-- Range count: number of `t : Fin n` with `a ≤ t.val < b` equals
    `b - a` (Nat truncated subtraction) when `b ≤ n`.  Holds for any
    `a, b` (when `a > b`, both sides are zero). -/
private theorem Fin.sumRat_count_range (n a b : Nat) (hbn : b ≤ n) :
    Fin.sumRat (fun t : Fin n => if a ≤ t.val ∧ t.val < b then (1 : Rat) else 0)
    = ((b - a : Nat) : Rat) := by
  by_cases hab : a ≤ b
  · rw [show (fun t : Fin n => if a ≤ t.val ∧ t.val < b then (1 : Rat) else 0)
          = (fun t : Fin n => (if t.val < b then (1 : Rat) else 0)
                                - (if t.val < a then (1 : Rat) else 0))
        from funext (fun t => indicator_range_eq_sub a b hab t.val)]
    rw [Fin.sumRat_sub]
    have han : a ≤ n := Nat.le_trans hab hbn
    rw [Fin.sumRat_count_lt n b hbn, Fin.sumRat_count_lt n a han]
    exact (Nat.cast_sub_rat a b hab).symm
  · have hab' : b < a := Nat.lt_of_not_le hab
    have hab'' : b ≤ a := Nat.le_of_lt hab'
    rw [show (fun t : Fin n => if a ≤ t.val ∧ t.val < b then (1 : Rat) else 0)
          = (fun _ : Fin n => (0 : Rat))
        from funext (fun t => by
          have hne : ¬(a ≤ t.val ∧ t.val < b) := fun ⟨h1, h2⟩ => by omega
          rw [if_neg hne])]
    rw [Fin.sumRat_const_zero]
    have hba : b - a = 0 := Nat.sub_eq_zero_of_le hab''
    rw [hba]; rfl

/-- **Envelope theorem** for the two-bidder Vickrey auction (discrete
    form, general).  In equilibrium under any prior, bidder 1's
    expected utility at type `v1` equals the cumulative allocation
    probability at lower types:

      U(v1) = Σ_{t : t.val < v1.val} Q(t).

    This is the discrete analogue of `U(v) = ∫_0^v Q(t) dt`. -/
theorem vickrey_envelope (n : Nat) (prior : Fin n → Rat) (v1 : Fin n) :
    vickreyEqUtility n prior v1 = vickreyEnvelopeIntegral n prior v1 := by
  unfold vickreyEqUtility vickreyEnvelopeIntegral vickreyAllocation
  -- Step 1: Replace (vickreyUtility val).cast with the count via
  -- Fin.sumRat_count_range, then factor prior(v2) inside the inner sum.
  rw [show (fun v2 : Fin n =>
              prior v2 * ((vickreyUtility n v1 v1 v2).val : Nat).cast)
        = (fun v2 : Fin n =>
              Fin.sumRat (fun t : Fin n =>
                if v2.val ≤ t.val ∧ t.val < v1.val then prior v2 else 0))
      from funext (fun v2 => by
        rw [vickreyUtility_val_eq n v1 v2]
        rw [(Fin.sumRat_count_range n v2.val v1.val
              (Nat.le_of_lt v1.isLt)).symm]
        rw [← Fin.sumRat_const_mul]
        apply Fin.sumRat_congr
        intro t
        by_cases h : v2.val ≤ t.val ∧ t.val < v1.val
        · rw [if_pos h, if_pos h, Rat.mul_one]
        · rw [if_neg h, if_neg h, Rat.mul_zero])]
  -- Step 2: Swap sums.
  rw [Fin.sumRat_swap (fun v2 t =>
        if v2.val ≤ t.val ∧ t.val < v1.val then prior v2 else 0)]
  -- Step 3: Match the RHS form pointwise per t.
  apply Fin.sumRat_congr
  intro t
  by_cases ht : t.val < v1.val
  · -- t.val < v1.val: inner sum simplifies to Σ_v2 (if v2.val ≤ t.val then prior else 0).
    rw [if_pos ht]
    apply Fin.sumRat_congr
    intro v2
    by_cases hv2 : v2.val ≤ t.val
    · rw [if_pos ⟨hv2, ht⟩, if_pos hv2]
    · rw [if_neg (fun ⟨h1, _⟩ => hv2 h1), if_neg hv2]
  · -- t.val ≥ v1.val: inner sum is 0.
    rw [if_neg ht]
    rw [show (fun v2 : Fin n =>
              if v2.val ≤ t.val ∧ t.val < v1.val then prior v2 else 0)
          = (fun _ : Fin n => (0 : Rat))
        from funext (fun v2 => by
          have hne : ¬(v2.val ≤ t.val ∧ t.val < v1.val) :=
            fun ⟨_, h2⟩ => ht h2
          rw [if_neg hne])]
    rw [Fin.sumRat_const_zero]

end AuctionCat
