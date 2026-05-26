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
  - (next)              identity (Kronecker delta), composition (matrix mul)
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

end FinStoch
end MarkovCat
