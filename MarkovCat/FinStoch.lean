import CompCatTheory.Foundation.Category

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

/-- Sum is linear: Σ (f + g) = Σ f + Σ g. -/
theorem Fin.sumRat_add : {n : Nat} → (f g : Fin n → Rat)
    → Fin.sumRat (fun i => f i + g i) = Fin.sumRat f + Fin.sumRat g
  | 0,     _, _ => by rw [Fin.sumRat_zero, Fin.sumRat_zero, Fin.sumRat_zero, Rat.add_zero]
  | k + 1, f, g => by
    rw [Fin.sumRat_succ, Fin.sumRat_succ, Fin.sumRat_succ]
    rw [Fin.sumRat_add (fun i => f i.succ) (fun i => g i.succ)]
    -- (f 0 + g 0) + (Σ f.succ + Σ g.succ) = (f 0 + Σ f.succ) + (g 0 + Σ g.succ)
    -- Manual rewrite of associativity / commutativity since Lean core has no `ring`.
    rw [Rat.add_assoc (f 0) (g 0)]
    rw [← Rat.add_assoc (g 0)]
    rw [Rat.add_comm (g 0) (Fin.sumRat _)]
    rw [Rat.add_assoc (Fin.sumRat _) (g 0)]
    rw [← Rat.add_assoc (f 0) (Fin.sumRat _) (g 0 + Fin.sumRat _)]

/-- Sum is homogeneous in a scalar: Σ (c * f i) = c * Σ f. -/
theorem Fin.sumRat_const_mul : {n : Nat} → (c : Rat) → (f : Fin n → Rat)
    → Fin.sumRat (fun i => c * f i) = c * Fin.sumRat f
  | 0,     c, _ => by rw [Fin.sumRat_zero, Fin.sumRat_zero, Rat.mul_zero]
  | k + 1, c, f => by
    rw [Fin.sumRat_succ, Fin.sumRat_succ]
    rw [Fin.sumRat_const_mul c (fun i => f i.succ)]
    rw [← Rat.mul_add]

/-- Double-sum swap (Fubini for finite sums). -/
theorem Fin.sumRat_swap : {m n : Nat} → (f : Fin m → Fin n → Rat)
    → Fin.sumRat (fun i => Fin.sumRat (fun j => f i j))
    = Fin.sumRat (fun j => Fin.sumRat (fun i => f i j))
  | 0,     n, f => by
    rw [Fin.sumRat_zero]
    rw [Fin.sumRat_congr (g := fun _ : Fin n => (0 : Rat))
          (fun _ => Fin.sumRat_zero _)]
    rw [Fin.sumRat_const_zero]
  | k + 1, n, f => by
    rw [Fin.sumRat_succ]
    rw [Fin.sumRat_swap (fun (i : Fin k) j => f i.succ j)]
    rw [← Fin.sumRat_add]
    apply Fin.sumRat_congr
    intro j
    exact (Fin.sumRat_succ (fun i => f i j)).symm

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

/-- The Kronecker delta is symmetric in its two indices. -/
theorem kron_symm {n : Nat} (i j : Fin n) : kron i j = kron j i := by
  unfold kron
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- Selector identity for the Kronecker delta on the left:
    Σ_l (kron i l * f l) = f i. -/
theorem sumRat_kron_mul : {n : Nat} → (i : Fin n) → (f : Fin n → Rat)
    → Fin.sumRat (fun l => kron i l * f l) = f i
  | 0, i, _ => i.elim0
  | k + 1, ⟨0, _⟩, f => by
    rw [Fin.sumRat_succ]
    have h0 : kron (⟨0, by omega⟩ : Fin (k + 1)) 0 = 1 := kron_self _
    rw [h0, Rat.one_mul]
    have hSucc : (l : Fin k)
        → kron (⟨0, by omega⟩ : Fin (k + 1)) l.succ * f l.succ = 0 := by
      intro l
      have hk : kron (⟨0, by omega⟩ : Fin (k + 1)) l.succ = 0 := by
        apply kron_ne
        intro heq
        have hval : (0 : Nat) = l.val + 1 := congrArg Fin.val heq
        omega
      rw [hk, Rat.zero_mul]
    rw [Fin.sumRat_congr hSucc, Fin.sumRat_const_zero]
    exact Rat.add_zero _
  | k + 1, ⟨v + 1, hv⟩, f => by
    rw [Fin.sumRat_succ]
    have h0 : kron (⟨v + 1, hv⟩ : Fin (k + 1)) 0 = 0 := by
      apply kron_ne
      intro heq
      have hval : v + 1 = (0 : Nat) := congrArg Fin.val heq
      omega
    rw [h0, Rat.zero_mul, Rat.zero_add]
    have hShift : (l : Fin k)
        → kron (⟨v + 1, hv⟩ : Fin (k + 1)) l.succ * f l.succ
        = kron (⟨v, by omega⟩ : Fin k) l * (fun l' : Fin k => f l'.succ) l := by
      intro l
      congr 1
      unfold kron
      by_cases hvl : v = l.val
      · have h1 : (⟨v + 1, hv⟩ : Fin (k + 1)) = l.succ := by
          apply Fin.ext
          show v + 1 = l.val + 1
          omega
        have h2 : (⟨v, by omega⟩ : Fin k) = l := by
          apply Fin.ext
          show v = l.val
          exact hvl
        rw [if_pos h1, if_pos h2]
      · have h1 : ¬((⟨v + 1, hv⟩ : Fin (k + 1)) = l.succ) := by
          intro heq
          apply hvl
          have hval : v + 1 = l.val + 1 := congrArg Fin.val heq
          omega
        have h2 : ¬((⟨v, by omega⟩ : Fin k) = l) := by
          intro heq
          apply hvl
          exact congrArg Fin.val heq
        rw [if_neg h1, if_neg h2]
    rw [Fin.sumRat_congr hShift]
    exact sumRat_kron_mul (⟨v, by omega⟩ : Fin k) (fun l : Fin k => f l.succ)

/-- Selector identity for the Kronecker delta on the right:
    Σ_l (f l * kron l j) = f j.  Follows from `sumRat_kron_mul` by
    commuting the product and the symmetry of `kron`. -/
theorem sumRat_mul_kron {n : Nat} (j : Fin n) (f : Fin n → Rat)
    : Fin.sumRat (fun l => f l * kron l j) = f j := by
  rw [Fin.sumRat_congr (fun l => Rat.mul_comm (f l) (kron l j))]
  rw [Fin.sumRat_congr (fun l => congrArg (· * f l) (kron_symm l j))]
  exact sumRat_kron_mul j f

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

/-! ## Composition (matrix multiplication) -/

/-- Composition of stochastic matrices via standard matrix multiplication:
    `(M ∘ N).entry i j = Σ_l M.entry i l * N.entry l j`.

    The non-negativity of the product follows from non-negativity of the
    factors plus non-negativity of finite sums of non-negatives.

    The row-sum-one property uses the Fubini swap, the homogeneity of
    sums, and the row-sum-one of both factors:
        Σ_j Σ_l M_il * N_lj
      = Σ_l Σ_j M_il * N_lj            (Fubini)
      = Σ_l (M_il * Σ_j N_lj)          (factor M_il out of inner sum)
      = Σ_l (M_il * 1)                 (N row sums to 1)
      = Σ_l M_il                       (mul by 1)
      = 1.                             (M row sums to 1) -/
def StochasticMatrix.comp {m k n : Nat}
    (M : StochasticMatrix m k) (N : StochasticMatrix k n)
    : StochasticMatrix m n where
  entry i j := Fin.sumRat (fun l : Fin k => M.entry i l * N.entry l j)
  nonneg i j :=
    Fin.sumRat_nonneg (fun l => Rat.mul_nonneg (M.nonneg i l) (N.nonneg l j))
  row_sum_one i := by
    rw [Fin.sumRat_swap (fun j l => M.entry i l * N.entry l j)]
    have hFactor : (l : Fin k)
        → Fin.sumRat (fun j => M.entry i l * N.entry l j)
        = M.entry i l * Fin.sumRat (fun j => N.entry l j) :=
      fun l => Fin.sumRat_const_mul (M.entry i l) (fun j => N.entry l j)
    rw [Fin.sumRat_congr hFactor]
    have hRowOne : (l : Fin k)
        → M.entry i l * Fin.sumRat (fun j => N.entry l j) = M.entry i l := by
      intro l
      rw [N.row_sum_one l]
      exact Rat.mul_one _
    rw [Fin.sumRat_congr hRowOne]
    exact M.row_sum_one i

/-- Extensionality for `StochasticMatrix`: equal entries determine
    equal matrices (the `nonneg` and `row_sum_one` fields are
    Prop-valued and hence proof-irrelevant). -/
@[ext]
theorem StochasticMatrix.ext {m n : Nat} {M N : StochasticMatrix m n}
    (h : (i : Fin m) → (j : Fin n) → M.entry i j = N.entry i j) : M = N := by
  cases M with | mk eM nM rM =>
  cases N with | mk eN nN rN =>
  have hEntry : eM = eN := by funext i j; exact h i j
  subst hEntry
  rfl

/-! ## Category axioms for `StochasticMatrix` -/

/-- Left identity: `idMatrix ∘ M = M`. -/
theorem StochasticMatrix.id_comp {m n : Nat} (M : StochasticMatrix m n)
    : (idMatrix m).comp M = M := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun l => (idMatrix m).entry i l * M.entry l j) = M.entry i j
  exact sumRat_kron_mul i (fun l => M.entry l j)

/-- Right identity: `M ∘ idMatrix = M`. -/
theorem StochasticMatrix.comp_id {m n : Nat} (M : StochasticMatrix m n)
    : M.comp (idMatrix n) = M := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun l => M.entry i l * (idMatrix n).entry l j) = M.entry i j
  exact sumRat_mul_kron j (fun l => M.entry i l)

/-- Associativity: `(M ∘ N) ∘ P = M ∘ (N ∘ P)`.

    Both sides expand to the triple sum
      `Σ_l Σ_q M_iq * N_ql * P_lj`
    (LHS via distributing P_lj across the inner sum on q; RHS via
    distributing M_iq across the inner sum on l).  These agree after
    a Fubini swap. -/
theorem StochasticMatrix.assoc {m k n p : Nat}
    (M : StochasticMatrix m k) (N : StochasticMatrix k n)
    (P : StochasticMatrix n p)
    : (M.comp N).comp P = M.comp (N.comp P) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun l => (Fin.sumRat (fun q => M.entry i q * N.entry q l))
                            * P.entry l j)
     = Fin.sumRat (fun q => M.entry i q
                            * Fin.sumRat (fun l => N.entry q l * P.entry l j))
  -- LHS: distribute P_lj across the inner sum
  have hLHS : (l : Fin n)
      → Fin.sumRat (fun q => M.entry i q * N.entry q l) * P.entry l j
      = Fin.sumRat (fun q => M.entry i q * N.entry q l * P.entry l j) := by
    intro l
    rw [Rat.mul_comm _ (P.entry l j)]
    rw [← Fin.sumRat_const_mul]
    apply Fin.sumRat_congr
    intro q
    exact Rat.mul_comm _ _
  rw [Fin.sumRat_congr hLHS]
  -- RHS: distribute M_iq across the inner sum
  have hRHS : (q : Fin k)
      → M.entry i q * Fin.sumRat (fun l => N.entry q l * P.entry l j)
      = Fin.sumRat (fun l => M.entry i q * N.entry q l * P.entry l j) := by
    intro q
    rw [← Fin.sumRat_const_mul]
    apply Fin.sumRat_congr
    intro l
    rw [← Rat.mul_assoc]
  rw [Fin.sumRat_congr hRHS]
  -- Now both sides are the same double sum, modulo Fubini swap
  exact Fin.sumRat_swap (fun l q => M.entry i q * N.entry q l * P.entry l j)

/-! ## Category instance -/

/-- `FinStoch` is the Markov category whose objects are natural numbers
    (interpreted as the finite sets `Fin n`) and whose morphisms are
    row-stochastic rational matrices.  The Category instance assembles
    the data and axioms proved above. -/
instance instCategoryNat : CompCatTheory.Category Nat where
  Hom := StochasticMatrix
  id := idMatrix
  comp := StochasticMatrix.comp
  id_comp := StochasticMatrix.id_comp
  comp_id := StochasticMatrix.comp_id
  assoc := StochasticMatrix.assoc

end FinStoch
end MarkovCat
