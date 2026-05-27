/-!
# MarkovCat.FinStoch

A concrete Markov category whose objects are natural numbers
(interpreted as the finite sets `Fin n`) and whose morphisms are
row-stochastic rational matrices.

Built on Lean 4 core without Mathlib: `Rat` is in `Init.Data.Rat`,
`Fin` and `Fin.succ` provide finite enumeration, and the relevant
arithmetic and ordering lemmas (`Rat.add_comm`, `Rat.mul_nonneg`,
etc.) are all in core.

Contents (built up across multiple commits):

  - `Fin.sumRat`        sum of a finite rational family (direct recursion)
  - sum lemmas          succ-unfolding, non-negativity, zero-family
  - `StochasticMatrix`  row-stochastic matrix of `Rat` values
  - `kron`              Kronecker delta as a Rat-valued indicator
  - `idMatrix`          stochastic identity (Kronecker delta on the diagonal)
  - (next)              composition (matrix multiplication)
  - (later)             Category / Monoidal / Markov instances on Nat
-/

set_option autoImplicit false

namespace MarkovCat
namespace FinStoch

/-! ## Finite sums of rationals -/

/-- Sum of a finite rational-valued family `f : Fin n → Rat`, defined by
    direct recursion on `n` so that `sumRat_zero` and `sumRat_succ` are
    definitional unfolding lemmas. -/
def Fin.sumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => f 0 + Fin.sumRat (fun i => f i.succ)

@[simp] theorem Fin.sumRat_zero (f : Fin 0 → Rat) : Fin.sumRat f = 0 := rfl

@[simp] theorem Fin.sumRat_succ {n : Nat} (f : Fin (n + 1) → Rat) :
    Fin.sumRat f = f 0 + Fin.sumRat (fun i => f i.succ) := rfl

/-- Sum of non-negative terms is non-negative. -/
theorem Fin.sumRat_nonneg : {n : Nat} → {f : Fin n → Rat}
    → ((i : Fin n) → 0 ≤ f i) → 0 ≤ Fin.sumRat f
  | 0,     _, _ => Rat.le_refl
  | _ + 1, _, h => by
    rw [Fin.sumRat_succ]
    exact Rat.add_nonneg (h 0) (Fin.sumRat_nonneg (fun i => h i.succ))

/-- Sum of a constantly zero family is zero. -/
theorem Fin.sumRat_const_zero : {n : Nat}
    → Fin.sumRat (fun _ : Fin n => (0 : Rat)) = 0
  | 0     => rfl
  | _ + 1 => by
    rw [Fin.sumRat_succ]
    rw [Fin.sumRat_const_zero]
    exact Rat.zero_add 0

/-- Pointwise-equal families have equal sums. -/
theorem Fin.sumRat_congr {n : Nat} {f g : Fin n → Rat}
    (h : (i : Fin n) → f i = g i) : Fin.sumRat f = Fin.sumRat g := by
  congr 1
  funext i
  exact h i

/-! ## Kronecker delta -/

/-- Rational-valued Kronecker delta: `1` when `i = j`, `0` otherwise. -/
def kron {n : Nat} (i j : Fin n) : Rat :=
  if i = j then 1 else 0

theorem kron_nonneg {n : Nat} (i j : Fin n) : 0 ≤ kron i j := by
  unfold kron
  if h : i = j then
    rw [if_pos h]; decide
  else
    rw [if_neg h]; decide

theorem kron_self {n : Nat} (i : Fin n) : kron i i = 1 := by
  unfold kron
  rw [if_pos rfl]

theorem kron_ne {n : Nat} {i j : Fin n} (h : i ≠ j) : kron i j = 0 := by
  unfold kron
  rw [if_neg h]

/-- The row sum of the Kronecker delta along a fixed row is `1`:
    only the diagonal entry contributes. -/
theorem sumRat_kron_eq_one : {n : Nat} → (i : Fin n)
    → Fin.sumRat (fun j => kron i j) = 1
  | 0, i => i.elim0
  | k + 1, ⟨0, _⟩ => by
    rw [Fin.sumRat_succ]
    -- LHS: kron ⟨0,_⟩ 0 + sumRat (fun j => kron ⟨0,_⟩ j.succ)
    have h0 : kron (⟨0, by omega⟩ : Fin (k + 1)) 0 = 1 := kron_self _
    have hSucc : (j : Fin k) → kron (⟨0, by omega⟩ : Fin (k + 1)) j.succ = 0 := by
      intro j
      apply kron_ne
      intro heq
      have : (⟨0, by omega⟩ : Fin (k + 1)).val = j.succ.val := by rw [heq]
      simp [Fin.succ] at this
    rw [h0]
    rw [Fin.sumRat_congr hSucc]
    rw [Fin.sumRat_const_zero]
    exact Rat.add_zero 1
  | k + 1, ⟨v + 1, hv⟩ => by
    rw [Fin.sumRat_succ]
    -- LHS: kron ⟨v+1,_⟩ 0 + sumRat (fun j => kron ⟨v+1,_⟩ j.succ)
    have h0 : kron (⟨v + 1, hv⟩ : Fin (k + 1)) 0 = 0 := by
      apply kron_ne
      intro heq
      have : (v + 1 : Nat) = 0 := by
        have := congrArg Fin.val heq
        simp at this
      omega
    have hShift : (j : Fin k)
        → kron (⟨v + 1, hv⟩ : Fin (k + 1)) j.succ
        = kron (⟨v, by omega⟩ : Fin k) j := by
      intro j
      unfold kron
      by_cases hvj : v = j.val
      · -- v = j.val: both Fin equalities hold, both ifs are 1
        have h1 : (⟨v + 1, hv⟩ : Fin (k + 1)) = j.succ := by
          apply Fin.ext
          show v + 1 = j.val + 1
          omega
        have h2 : (⟨v, by omega⟩ : Fin k) = j := by
          apply Fin.ext
          show v = j.val
          exact hvj
        rw [if_pos h1, if_pos h2]
      · -- v ≠ j.val: both Fin equalities fail, both ifs are 0
        have h1 : ¬((⟨v + 1, hv⟩ : Fin (k + 1)) = j.succ) := by
          intro heq
          apply hvj
          have hval : v + 1 = j.val + 1 := congrArg Fin.val heq
          omega
        have h2 : ¬((⟨v, by omega⟩ : Fin k) = j) := by
          intro heq
          apply hvj
          exact congrArg Fin.val heq
        rw [if_neg h1, if_neg h2]
    rw [h0]
    rw [Fin.sumRat_congr hShift]
    rw [sumRat_kron_eq_one (⟨v, by omega⟩ : Fin k)]
    exact Rat.zero_add 1

/-! ## Stochastic matrices -/

/-- A row-stochastic `m × n` matrix of `Rat` entries.  The constraints
    capture exactly what is needed for the matrix to represent a
    stochastic kernel `Fin m → Fin n`:

      - Every entry is non-negative.
      - Every row sums to one. -/
structure StochasticMatrix (m n : Nat) where
  /-- The underlying matrix of `Rat` entries. -/
  entry : Fin m → Fin n → Rat
  /-- Non-negativity: every entry is at least 0. -/
  nonneg : (i : Fin m) → (j : Fin n) → 0 ≤ entry i j
  /-- Row stochastic: every row sums to 1. -/
  row_sum_one : (i : Fin m) → Fin.sumRat (fun j => entry i j) = 1

/-! ## Identity matrix -/

/-- The identity stochastic matrix: the Kronecker delta on the diagonal. -/
def idMatrix (n : Nat) : StochasticMatrix n n where
  entry := kron
  nonneg := kron_nonneg
  row_sum_one := sumRat_kron_eq_one

end FinStoch
end MarkovCat
