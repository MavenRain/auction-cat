import AuctionCat.SecondPrice

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

end AuctionCat
