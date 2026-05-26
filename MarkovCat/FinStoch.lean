/-!
# MarkovCat.FinStoch

A concrete Markov category whose objects are natural numbers
(interpreted as the finite sets `Fin n`) and whose morphisms are
row-stochastic rational matrices.

Built on Lean 4 core without Mathlib: `Rat` is in `Init.Data.Rat`,
`Fin.foldl` provides finite enumeration, and the relevant arithmetic
and ordering lemmas (`Rat.add_comm`, `Rat.mul_nonneg`, etc.) are all
in core.

Contents (built up across multiple commits):

  - `Fin.sumRat`        sum of a finite rational family
  - `StochasticMatrix`  row-stochastic matrix of `Rat` values
  - (later) `Category` / `MonoidalCategory` / `SymmetricMonoidalCategory`
                        / `MarkovCategory` instances on `Nat`
-/

set_option autoImplicit false

namespace MarkovCat
namespace FinStoch

/-- Sum of a finite rational-valued family `f : Fin n → Rat`. -/
def Fin.sumRat {n : Nat} (f : Fin n → Rat) : Rat :=
  Fin.foldl n (fun acc i => acc + f i) 0

/-- Sum of zero terms is zero. -/
@[simp] theorem Fin.sumRat_zero (f : Fin 0 → Rat) : Fin.sumRat f = 0 :=
  _root_.Fin.foldl_zero _ _

/-- A row-stochastic `m × n` matrix of `Rat` entries.

    The constraints capture exactly what is needed for the matrix to
    represent a stochastic kernel `Fin m → Fin n`:

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
