import CompCatTheory.Foundation.Category
import CompCatTheory.Foundation.Product

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

open CompCatTheory

namespace MarkovCat
namespace FinStoch

/-! ## Fin pairing (for the Kronecker product)

The pairing `Fin m × Fin n → Fin (m * n)` encodes `(a, b)` as
`m * b.val + a.val` so that `b` indexes contiguous blocks of size `m`.
This aligns with `Nat.mul` recursing on the second argument: peeling
off the last block (`b = n - 1`) corresponds to `Nat.mul_succ`'s
`m * (k+1) = m * k + m` splitting. -/

/-- Pairing `Fin m × Fin n → Fin (m * n)`: encode `(a, b)` as
    `m * b.val + a.val`. -/
def Fin.pair {m n : Nat} (a : Fin m) (b : Fin n) : Fin (m * n) :=
  ⟨m * b.val + a.val, by
    have ha : a.val < m := a.isLt
    have hb : b.val + 1 ≤ n := b.isLt
    have hStep : m * b.val + a.val < m * b.val + m := by
      omega
    have hSucc : m * b.val + m = m * (b.val + 1) := by
      rw [Nat.mul_succ]
    have hBound : m * (b.val + 1) ≤ m * n :=
      Nat.mul_le_mul_left m hb
    omega⟩

@[simp] theorem Fin.pair_val {m n : Nat} (a : Fin m) (b : Fin n) :
    (Fin.pair a b).val = m * b.val + a.val := rfl

/-- Project `Fin (m * n)` to its first component `Fin m`: the inner
    position within a block, recovered via Nat modulo. -/
def Fin.first {m n : Nat} (x : Fin (m * n)) : Fin m :=
  ⟨x.val % m, by
    by_cases hm : 0 < m
    · exact Nat.mod_lt _ hm
    · have hm0 : m = 0 := by omega
      have hMul : m * n = 0 := by rw [hm0, Nat.zero_mul]
      have := x.isLt
      omega⟩

/-- Project `Fin (m * n)` to its second component `Fin n`: the outer
    block index, recovered via Nat division. -/
def Fin.second {m n : Nat} (x : Fin (m * n)) : Fin n :=
  ⟨x.val / m, by
    by_cases hm : 0 < m
    · have hLt : x.val < n * m := by rw [Nat.mul_comm n m]; exact x.isLt
      exact (Nat.div_lt_iff_lt_mul hm).mpr hLt
    · have hm0 : m = 0 := by omega
      have hMul : m * n = 0 := by rw [hm0, Nat.zero_mul]
      have := x.isLt
      omega⟩

@[simp] theorem Fin.first_val {m n : Nat} (x : Fin (m * n)) :
    (Fin.first x).val = x.val % m := rfl

@[simp] theorem Fin.second_val {m n : Nat} (x : Fin (m * n)) :
    (Fin.second x).val = x.val / m := rfl

/-- Round trip on the first component: `first (pair a b) = a`. -/
theorem Fin.first_pair {m n : Nat} (a : Fin m) (b : Fin n) :
    Fin.first (Fin.pair a b) = a := by
  apply Fin.ext
  show (m * b.val + a.val) % m = a.val
  rw [Nat.mul_comm m b.val, Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt a.isLt

/-- Round trip on the second component: `second (pair a b) = b` (when `m > 0`). -/
theorem Fin.second_pair {m n : Nat} (hm : 0 < m) (a : Fin m) (b : Fin n) :
    Fin.second (Fin.pair a b) = b := by
  apply Fin.ext
  show (m * b.val + a.val) / m = b.val
  rw [Nat.mul_comm m b.val, Nat.add_comm]
  rw [Nat.add_mul_div_right _ _ hm]
  rw [Nat.div_eq_of_lt a.isLt]
  exact Nat.zero_add b.val

/-- Reconstruction: pairing the first and second projections recovers
    the original index. -/
theorem Fin.pair_first_second {m n : Nat} (x : Fin (m * n)) :
    Fin.pair (Fin.first x) (Fin.second x) = x := by
  apply Fin.ext
  show m * (x.val / m) + x.val % m = x.val
  exact Nat.div_add_mod x.val m

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

/-- Sum over a singleton index family: just the single element. -/
@[simp] theorem Fin.sumRat_fin_one (f : Fin 1 → Rat) :
    Fin.sumRat f = f 0 := by
  show f 0 + Fin.sumRat (fun i : Fin 0 => f i.succ) = f 0
  rw [Fin.sumRat_zero]
  exact Rat.add_zero _

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

/-- Peel-from-the-right form of `sumRat_succ`:
    `Σ g = Σ (g restricted to the first n) + g (last)`. -/
theorem Fin.sumRat_succ_right : (n : Nat) → (g : Fin (n + 1) → Rat)
    → Fin.sumRat g
    = Fin.sumRat (fun a : Fin n => g ⟨a.val, by omega⟩) + g ⟨n, by omega⟩
  | 0, g => by
    rw [Fin.sumRat_succ, Fin.sumRat_zero, Fin.sumRat_zero, Rat.add_zero, Rat.zero_add]
    exact congrArg g (Fin.ext rfl)
  | k + 1, g => by
    rw [Fin.sumRat_succ]
    rw [Fin.sumRat_succ_right k (fun i => g i.succ)]
    rw [Fin.sumRat_succ (n := k) (fun a : Fin (k + 1) => g ⟨a.val, by omega⟩)]
    rw [Rat.add_assoc]
    congr 1

/-- Splitting a sum at a position: the sum over `Fin (m + n)` factors
    as the sum over the first `m` entries plus the sum over the
    remaining `n` entries (shifted by `m`). -/
theorem Fin.sumRat_split : {m : Nat} → (n : Nat) → (f : Fin (m + n) → Rat)
    → Fin.sumRat f
    = Fin.sumRat (fun a : Fin m => f ⟨a.val, by omega⟩)
      + Fin.sumRat (fun b : Fin n => f ⟨m + b.val, by omega⟩)
  | m, 0, f => by
    rw [Fin.sumRat_zero, Rat.add_zero]
    apply Fin.sumRat_congr
    intro a
    exact congrArg f (Fin.ext rfl)
  | m, k + 1, f => by
    rw [Fin.sumRat_succ_right (m + k) f]
    rw [Fin.sumRat_split (m := m) k (fun a => f ⟨a.val, by omega⟩)]
    rw [Fin.sumRat_succ_right k (fun b : Fin (k + 1) => f ⟨m + b.val, by omega⟩)]
    rw [Rat.add_assoc]

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

/-- Unpairing identity for finite sums: a sum over `Fin (m * n)` factors
    as a double sum over `Fin m × Fin n` via `Fin.pair`.

    Proved by induction on n.  The base case uses `m * 0 = 0` def-eq.
    The step case uses `m * (k+1) = m * k + m` def-eq, then
    `sumRat_split` at position `m * k` (separating the `Fin (m * k)`
    initial part from the trailing `Fin m`), then the IH on the first
    part, then massaging the RHS via `sumRat_succ_right` and
    `sumRat_add`. -/
theorem Fin.sumRat_unpair : (m : Nat) → (n : Nat) → (f : Fin (m * n) → Rat)
    → Fin.sumRat f
    = Fin.sumRat (fun a : Fin m => Fin.sumRat (fun b : Fin n => f (Fin.pair a b)))
  | m, 0, f => by
    rw [Fin.sumRat_zero]
    rw [show (fun a : Fin m => Fin.sumRat (fun b : Fin 0 => f (Fin.pair a b)))
        = (fun _ : Fin m => (0 : Rat)) from funext (fun _ => Fin.sumRat_zero _)]
    rw [Fin.sumRat_const_zero]
  | m, k + 1, f => by
    rw [Fin.sumRat_split (m := m * k) m f]
    rw [Fin.sumRat_unpair m k (fun i : Fin (m * k) =>
      f ⟨i.val, by
        have hStep : m * k ≤ m * (k + 1) := Nat.mul_le_mul_left m (Nat.le_succ k)
        omega⟩)]
    rw [show (fun a : Fin m => Fin.sumRat (fun b : Fin (k + 1) => f (Fin.pair a b)))
        = (fun a : Fin m => Fin.sumRat (fun b' : Fin k =>
                                          f (Fin.pair a ⟨b'.val, by omega⟩))
                            + f (Fin.pair a ⟨k, by omega⟩)) from
        funext (fun a => Fin.sumRat_succ_right k (fun b => f (Fin.pair a b)))]
    rw [Fin.sumRat_add (fun a : Fin m =>
                          Fin.sumRat (fun b' : Fin k =>
                                        f (Fin.pair a ⟨b'.val, by omega⟩)))
                       (fun a : Fin m => f (Fin.pair a ⟨k, by omega⟩))]
    congr 1

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

/-- A stochastic matrix with at least one row has at least one column.

    If `k = 0`, every row's sum is `Σ over Fin 0 = 0`, but the
    `row_sum_one` field of a `StochasticMatrix` requires that sum to
    be `1`.  So `k = 0` and `m > 0` is contradictory. -/
private theorem StochasticMatrix.cols_pos {m k : Nat}
    (M : StochasticMatrix m k) (hm : 0 < m) : 0 < k := by
  cases k with
  | zero =>
    have hrow := M.row_sum_one ⟨0, hm⟩
    rw [Fin.sumRat_zero] at hrow
    exact absurd hrow (by decide)
  | succ k' => exact Nat.succ_pos k'

/-! ## Identity matrix -/

/-- The identity stochastic matrix: the Kronecker delta on the diagonal. -/
def idMatrix (n : Nat) : StochasticMatrix n n where
  entry := kron
  nonneg := kron_nonneg
  row_sum_one := sumRat_kron_eq_one

/-! ## Kronecker product (the monoidal tensor on `FinStoch`) -/

/-- Kronecker product of stochastic matrices.

    `(M ⊗ N).entry x y = M.entry (first x) (first y) * N.entry (second x) (second y)`

    where `first x : Fin m` is the inner index and `second x : Fin m'`
    is the outer (block) index of `x : Fin (m * m')`. -/
def StochasticMatrix.kron {m k m' k' : Nat}
    (M : StochasticMatrix m k) (N : StochasticMatrix m' k')
    : StochasticMatrix (m * m') (k * k') where
  entry x y :=
    M.entry (Fin.first x) (Fin.first y) * N.entry (Fin.second x) (Fin.second y)
  nonneg _ _ :=
    Rat.mul_nonneg (M.nonneg _ _) (N.nonneg _ _)
  row_sum_one x := by
    -- Derive positivity of m, m', k, k'.
    have hmm' : 0 < m * m' := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
    have hm : 0 < m := Nat.pos_of_mul_pos_right hmm'
    have hm' : 0 < m' := Nat.pos_of_mul_pos_left hmm'
    have hk : 0 < k := M.cols_pos hm
    -- Factor the sum over Fin (k * k') as a double sum.
    rw [Fin.sumRat_unpair k k' _]
    -- After Fin.first_pair / Fin.second_pair, the inner sum factors as
    -- M.entry (first x) c * N.entry (second x) d
    rw [show (fun c : Fin k => Fin.sumRat (fun d : Fin k' =>
            M.entry (Fin.first x) (Fin.first (Fin.pair c d))
              * N.entry (Fin.second x) (Fin.second (Fin.pair c d))))
        = (fun c : Fin k => Fin.sumRat (fun d : Fin k' =>
            M.entry (Fin.first x) c * N.entry (Fin.second x) d)) from
        funext (fun c => Fin.sumRat_congr (fun d => by
          rw [Fin.first_pair c d, Fin.second_pair hk c d]))]
    -- Factor M.entry out of the inner sum (it does not depend on d).
    rw [show (fun c : Fin k => Fin.sumRat (fun d : Fin k' =>
            M.entry (Fin.first x) c * N.entry (Fin.second x) d))
        = (fun c : Fin k =>
            M.entry (Fin.first x) c
              * Fin.sumRat (fun d : Fin k' => N.entry (Fin.second x) d)) from
        funext (fun c => Fin.sumRat_const_mul _ _)]
    -- N's row sum is 1.
    rw [show (fun c : Fin k =>
            M.entry (Fin.first x) c
              * Fin.sumRat (fun d : Fin k' => N.entry (Fin.second x) d))
        = (fun c : Fin k => M.entry (Fin.first x) c) from
        funext (fun c => by
          rw [N.row_sum_one (Fin.second x)]; exact Rat.mul_one _)]
    -- M's row sum is 1.
    exact M.row_sum_one (Fin.first x)

/-- Auxiliary: reorder a four-term product `(a * b) * (c * d) = (a * c) * (b * d)`.
    Used in the Kronecker-mixed-product proof. -/
private theorem mul_swap4 (a b c d : Rat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Rat.mul_assoc a b (c * d)]
  rw [← Rat.mul_assoc b c d]
  rw [Rat.mul_comm b c]
  rw [Rat.mul_assoc c b d]
  rw [← Rat.mul_assoc a c (b * d)]

/-- A product of finite sums distributes as a double sum:
    `(Σ_l f l) * (Σ_l' g l') = Σ_l Σ_l' (f l * g l')`. -/
theorem Fin.sumRat_mul_sumRat {k k' : Nat}
    (f : Fin k → Rat) (g : Fin k' → Rat) :
    (Fin.sumRat f) * (Fin.sumRat g)
    = Fin.sumRat (fun l : Fin k => Fin.sumRat (fun l' : Fin k' => f l * g l')) := by
  -- (Σ f) * (Σ g) = (Σ g) * (Σ f)    [mul_comm]
  --              = Σ_l ((Σ g) * f l)  [← sumRat_const_mul]
  --              = Σ_l (f l * Σ g)    [mul_comm in summand]
  --              = Σ_l Σ_l' (f l * g l')   [← sumRat_const_mul in each summand]
  rw [Rat.mul_comm (Fin.sumRat f) (Fin.sumRat g)]
  rw [← Fin.sumRat_const_mul (Fin.sumRat g) f]
  apply Fin.sumRat_congr
  intro l
  rw [Rat.mul_comm (Fin.sumRat g) (f l)]
  rw [← Fin.sumRat_const_mul (f l) g]

/-- The Kronecker product of identity matrices is the identity. -/
theorem StochasticMatrix.kron_identity (m n : Nat) :
    StochasticMatrix.kron (idMatrix m) (idMatrix n) = idMatrix (m * n) := by
  apply StochasticMatrix.ext
  intro x y
  have hLHS :
      (StochasticMatrix.kron (idMatrix m) (idMatrix n)).entry x y
      = MarkovCat.FinStoch.kron (Fin.first x) (Fin.first y)
        * MarkovCat.FinStoch.kron (Fin.second x) (Fin.second y) := rfl
  have hRHS : (idMatrix (m * n)).entry x y = MarkovCat.FinStoch.kron x y := rfl
  rw [hLHS, hRHS]
  by_cases hxy : x = y
  · subst hxy
    simp only [kron_self]
    exact Rat.one_mul 1
  · rw [kron_ne hxy]
    by_cases h1 : Fin.first x = Fin.first y
    · have h2 : Fin.second x ≠ Fin.second y := by
        intro h2
        apply hxy
        have hPair :
            Fin.pair (Fin.first x) (Fin.second x)
            = Fin.pair (Fin.first y) (Fin.second y) := by
          rw [h1, h2]
        rw [Fin.pair_first_second, Fin.pair_first_second] at hPair
        exact hPair
      rw [kron_ne h2, Rat.mul_zero]
    · rw [kron_ne h1, Rat.zero_mul]

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

/-- Mixed-product property of the Kronecker product:
    `(M₁ ∘ M₂) ⊗ (N₁ ∘ N₂) = (M₁ ⊗ N₁) ∘ (M₂ ⊗ N₂)`.

    This is the `map_comp` obligation for the tensor functor on FinStoch. -/
theorem StochasticMatrix.kron_comp {m k n m' k' n' : Nat}
    (M₁ : StochasticMatrix m k) (M₂ : StochasticMatrix k n)
    (N₁ : StochasticMatrix m' k') (N₂ : StochasticMatrix k' n') :
    StochasticMatrix.kron (M₁.comp M₂) (N₁.comp N₂)
    = (StochasticMatrix.kron M₁ N₁).comp (StochasticMatrix.kron M₂ N₂) := by
  apply StochasticMatrix.ext
  intro x y
  -- Derive 0 < k to feed second_pair on Fin (k * k') indices.
  have hmm' : 0 < m * m' := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hm : 0 < m := Nat.pos_of_mul_pos_right hmm'
  have hk : 0 < k := M₁.cols_pos hm
  -- Expand both sides to their underlying sum forms.
  show (Fin.sumRat (fun l : Fin k =>
            M₁.entry (Fin.first x) l * M₂.entry l (Fin.first y)))
        * (Fin.sumRat (fun l' : Fin k' =>
            N₁.entry (Fin.second x) l' * N₂.entry l' (Fin.second y)))
     = Fin.sumRat (fun z : Fin (k * k') =>
          M₁.entry (Fin.first x) (Fin.first z) * N₁.entry (Fin.second x) (Fin.second z)
          * (M₂.entry (Fin.first z) (Fin.first y) * N₂.entry (Fin.second z) (Fin.second y)))
  -- LHS: distribute the product of finite sums into a double sum.
  rw [Fin.sumRat_mul_sumRat]
  -- RHS: apply sumRat_unpair to break Fin (k * k') into Fin k × Fin k'.
  rw [Fin.sumRat_unpair k k' _]
  -- Substitute first (pair e f) = e, second (pair e f) = f.
  rw [show (fun e : Fin k => Fin.sumRat (fun f : Fin k' =>
              M₁.entry (Fin.first x) (Fin.first (Fin.pair e f))
                * N₁.entry (Fin.second x) (Fin.second (Fin.pair e f))
              * (M₂.entry (Fin.first (Fin.pair e f)) (Fin.first y)
                  * N₂.entry (Fin.second (Fin.pair e f)) (Fin.second y))))
      = (fun e : Fin k => Fin.sumRat (fun f : Fin k' =>
              (M₁.entry (Fin.first x) e * N₁.entry (Fin.second x) f)
              * (M₂.entry e (Fin.first y) * N₂.entry f (Fin.second y)))) from
      funext (fun e => Fin.sumRat_congr (fun f => by
        rw [Fin.first_pair e f, Fin.second_pair hk e f]))]
  -- Reorder each summand via mul_swap4.
  apply Fin.sumRat_congr
  intro e
  apply Fin.sumRat_congr
  intro f
  exact mul_swap4 _ _ _ _

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

/-! ## Tensor product as a bifunctor -/

/-- The Kronecker product assembled as a bifunctor
    `(- ⊗ -) : Nat × Nat ⥤ Nat` on the FinStoch category.

    - On objects: `(m, n) ↦ m * n`.
    - On morphisms: `(M, N) ↦ M ⊗ N` (Kronecker product).

    The functoriality obligations are exactly `kron_identity` and
    `kron_comp` proved above.  This is the data that the eventual
    `MonoidalCategory` instance consumes for its `tensor` field; the
    associator, unitors, and pentagon/triangle coherences are built on
    top of this. -/
def tensorFunctor : (Nat × Nat) ⥤ Nat where
  obj := fun mn => mn.1 * mn.2
  map := fun MN => StochasticMatrix.kron MN.1 MN.2
  map_id := fun mn => StochasticMatrix.kron_identity mn.1 mn.2
  map_comp := fun MN MN' =>
    StochasticMatrix.kron_comp MN.1 MN'.1 MN.2 MN'.2

/-! ## Left and right unitors

  The monoidal unit on FinStoch is the natural number `1`.  Because
  `1 * X = X` and `X * 1 = X` only hold propositionally (not
  definitionally), the unitors are non-trivial deterministic
  stochastic matrices that re-index `Fin (1 * X)` (resp. `Fin (X * 1)`)
  to `Fin X` via the pairing projections. -/

/-- The left unitor `1 ⊗ X → X`, expressed as a stochastic matrix
    `StochasticMatrix (1 * X) X`.

    `Fin (1 * X)` is the set of pairs `(0, b)` with `b : Fin X`; this
    matrix sends each input `i` to its second component
    `Fin.second i : Fin X` and assigns mass `1` to the matching
    column. -/
def leftUnitor (X : Nat) : StochasticMatrix (1 * X) X where
  entry i j := kron (Fin.second i) j
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := sumRat_kron_eq_one (Fin.second i)

/-- The right unitor `X ⊗ 1 → X`, projecting onto the first component
    of the pair `(a, 0) : Fin X × Fin 1` represented by
    `i : Fin (X * 1)`. -/
def rightUnitor (X : Nat) : StochasticMatrix (X * 1) X where
  entry i j := kron (Fin.first i) j
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := sumRat_kron_eq_one (Fin.first i)

/-- Inverse of the left unitor: embed `i : Fin X` into `Fin (1 * X)`
    as the unique element with second component `i`. -/
def leftUnitorInv (X : Nat) : StochasticMatrix X (1 * X) where
  entry i j := kron i (Fin.second j)
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := by
    show Fin.sumRat (fun j : Fin (1 * X) => kron i (Fin.second j)) = 1
    rw [Fin.sumRat_unpair 1 X _]
    rw [show (fun a : Fin 1 => Fin.sumRat (fun b : Fin X =>
                                  kron i (Fin.second (Fin.pair a b))))
        = (fun _ : Fin 1 => Fin.sumRat (fun b : Fin X => kron i b)) from
        funext (fun a => Fin.sumRat_congr (fun b => by
          rw [Fin.second_pair Nat.one_pos a b]))]
    rw [show (fun _ : Fin 1 => Fin.sumRat (fun b : Fin X => kron i b))
        = (fun _ : Fin 1 => (1 : Rat)) from
        funext (fun _ => sumRat_kron_eq_one i)]
    exact Fin.sumRat_fin_one (fun _ => 1)

/-- Inverse of the right unitor: embed `i : Fin X` into `Fin (X * 1)`
    as the unique element with first component `i`. -/
def rightUnitorInv (X : Nat) : StochasticMatrix X (X * 1) where
  entry i j := kron i (Fin.first j)
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := by
    show Fin.sumRat (fun j : Fin (X * 1) => kron i (Fin.first j)) = 1
    rw [Fin.sumRat_unpair X 1 _]
    rw [show (fun a : Fin X => Fin.sumRat (fun b : Fin 1 =>
                                  kron i (Fin.first (Fin.pair a b))))
        = (fun a : Fin X => Fin.sumRat (fun _ : Fin 1 => kron i a)) from
        funext (fun a => Fin.sumRat_congr (fun b => by
          rw [Fin.first_pair a b]))]
    rw [show (fun a : Fin X => Fin.sumRat (fun _ : Fin 1 => kron i a))
        = (fun a : Fin X => kron i a) from
        funext (fun a => Fin.sumRat_fin_one (fun _ => kron i a))]
    exact sumRat_kron_eq_one i

/-! ## Isomorphism laws for the unitors

  In `Fin (1 * X)`, the first projection `Fin.first` lands in `Fin 1`
  and is forced to `0`, so `i = j` iff `Fin.second i = Fin.second j`.
  Symmetrically for `Fin (X * 1)` with `Fin.first`.  These two facts
  reduce each iso law to a single `sumRat_kron_mul` application. -/

/-- For `i, j : Fin (1 * X)`, the Kronecker delta is preserved by the
    second projection (which is a bijection `Fin (1 * X) ≃ Fin X`). -/
private theorem kron_second_eq_left {X : Nat} (i j : Fin (1 * X)) :
    kron (Fin.second i) (Fin.second j) = kron i j := by
  unfold kron
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hij]
    have hne : Fin.second i ≠ Fin.second j := by
      intro hs
      apply hij
      apply Fin.ext
      have hsVal : (Fin.second i).val = (Fin.second j).val := by rw [hs]
      rw [Fin.second_val, Fin.second_val] at hsVal
      rw [Nat.div_one, Nat.div_one] at hsVal
      exact hsVal
    rw [if_neg hne]

/-- For `i, j : Fin (X * 1)`, the Kronecker delta is preserved by the
    first projection (which is a bijection `Fin (X * 1) ≃ Fin X`). -/
private theorem kron_first_eq_right {X : Nat} (i j : Fin (X * 1)) :
    kron (Fin.first i) (Fin.first j) = kron i j := by
  unfold kron
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hij]
    have hne : Fin.first i ≠ Fin.first j := by
      intro hs
      apply hij
      apply Fin.ext
      have hsVal : (Fin.first i).val = (Fin.first j).val := by rw [hs]
      rw [Fin.first_val, Fin.first_val] at hsVal
      have hi : i.val < X := by
        have hil := i.isLt
        have hmul : X * 1 = X := Nat.mul_one X
        omega
      have hj : j.val < X := by
        have hjl := j.isLt
        have hmul : X * 1 = X := Nat.mul_one X
        omega
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hsVal
      exact hsVal
    rw [if_neg hne]

/-- `leftUnitor ≫ leftUnitorInv = 𝟙_{1*X}`. -/
theorem leftUnitor_hom_inv (X : Nat) :
    (leftUnitor X).comp (leftUnitorInv X) = idMatrix (1 * X) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin X => kron (Fin.second i) k * kron k (Fin.second j))
     = kron i j
  rw [sumRat_kron_mul (Fin.second i) (fun k : Fin X => kron k (Fin.second j))]
  exact kron_second_eq_left i j

/-- `leftUnitorInv ≫ leftUnitor = 𝟙_X`. -/
theorem leftUnitor_inv_hom (X : Nat) :
    (leftUnitorInv X).comp (leftUnitor X) = idMatrix X := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin (1 * X) => kron i (Fin.second k) * kron (Fin.second k) j)
     = kron i j
  rw [Fin.sumRat_unpair 1 X _]
  rw [show (fun a : Fin 1 => Fin.sumRat (fun b : Fin X =>
                kron i (Fin.second (Fin.pair a b))
                * kron (Fin.second (Fin.pair a b)) j))
      = (fun _ : Fin 1 => Fin.sumRat (fun b : Fin X => kron i b * kron b j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [Fin.second_pair Nat.one_pos a b]))]
  rw [Fin.sumRat_fin_one (fun _ : Fin 1 =>
        Fin.sumRat (fun b : Fin X => kron i b * kron b j))]
  exact sumRat_kron_mul i (fun b : Fin X => kron b j)

/-- `rightUnitor ≫ rightUnitorInv = 𝟙_{X*1}`. -/
theorem rightUnitor_hom_inv (X : Nat) :
    (rightUnitor X).comp (rightUnitorInv X) = idMatrix (X * 1) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin X => kron (Fin.first i) k * kron k (Fin.first j))
     = kron i j
  rw [sumRat_kron_mul (Fin.first i) (fun k : Fin X => kron k (Fin.first j))]
  exact kron_first_eq_right i j

/-- `rightUnitorInv ≫ rightUnitor = 𝟙_X`. -/
theorem rightUnitor_inv_hom (X : Nat) :
    (rightUnitorInv X).comp (rightUnitor X) = idMatrix X := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin (X * 1) => kron i (Fin.first k) * kron (Fin.first k) j)
     = kron i j
  rw [Fin.sumRat_unpair X 1 _]
  rw [show (fun a : Fin X => Fin.sumRat (fun b : Fin 1 =>
                kron i (Fin.first (Fin.pair a b))
                * kron (Fin.first (Fin.pair a b)) j))
      = (fun a : Fin X => Fin.sumRat (fun _ : Fin 1 => kron i a * kron a j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [Fin.first_pair a b]))]
  rw [show (fun a : Fin X => Fin.sumRat (fun _ : Fin 1 => kron i a * kron a j))
      = (fun a : Fin X => kron i a * kron a j) from
      funext (fun a => Fin.sumRat_fin_one _)]
  exact sumRat_kron_mul i (fun a : Fin X => kron a j)

/-! ## Naturality of the unitors

  Both unitors are natural transformations: tensoring with `idMatrix 1`
  on the unit side commutes with applying the underlying morphism on
  the non-unit side, modulo the unitor's re-indexing. -/

/-- The Kronecker delta on `Fin 1` is always `1`: both arguments are
    forced to the unique element. -/
private theorem kron_fin_one (a b : Fin 1) : kron a b = 1 := by
  have hab : a = b := by
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    omega
  rw [hab]
  exact kron_self b

/-- Left-unitor naturality: `(𝟙_{1} ⊗ f) ≫ leftUnitor Y = leftUnitor X ≫ f`. -/
theorem leftUnitor_naturality {X Y : Nat} (f : StochasticMatrix X Y) :
    (StochasticMatrix.kron (idMatrix 1) f).comp (leftUnitor Y)
    = (leftUnitor X).comp f := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin (1 * Y) =>
        (kron (Fin.first i) (Fin.first k)
          * f.entry (Fin.second i) (Fin.second k))
        * kron (Fin.second k) j)
     = Fin.sumRat (fun k : Fin X => kron (Fin.second i) k * f.entry k j)
  -- RHS collapses to f.entry (Fin.second i) j via sumRat_kron_mul.
  rw [sumRat_kron_mul (Fin.second i) (fun k : Fin X => f.entry k j)]
  -- Expand LHS via sumRat_unpair on Fin (1 * Y).
  rw [Fin.sumRat_unpair 1 Y _]
  -- Replace Fin.first / Fin.second on pair a b with a / b.
  rw [show (fun a : Fin 1 => Fin.sumRat (fun b : Fin Y =>
              (kron (Fin.first i) (Fin.first (Fin.pair a b))
                * f.entry (Fin.second i) (Fin.second (Fin.pair a b)))
              * kron (Fin.second (Fin.pair a b)) j))
      = (fun a : Fin 1 => Fin.sumRat (fun b : Fin Y =>
              (kron (Fin.first i) a * f.entry (Fin.second i) b)
              * kron b j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [Fin.first_pair a b, Fin.second_pair Nat.one_pos a b]))]
  -- Collapse the trivial Fin 1 factor using kron_fin_one.
  rw [show (fun a : Fin 1 => Fin.sumRat (fun b : Fin Y =>
              (kron (Fin.first i) a * f.entry (Fin.second i) b)
              * kron b j))
      = (fun _ : Fin 1 => Fin.sumRat (fun b : Fin Y =>
              f.entry (Fin.second i) b * kron b j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [kron_fin_one (Fin.first i) a, Rat.one_mul]))]
  -- Outer sum is over Fin 1 of a constant.
  rw [Fin.sumRat_fin_one (fun _ : Fin 1 =>
        Fin.sumRat (fun b : Fin Y => f.entry (Fin.second i) b * kron b j))]
  -- Inner sum collapses via sumRat_mul_kron.
  exact sumRat_mul_kron j (fun b : Fin Y => f.entry (Fin.second i) b)

/-- Right-unitor naturality: `(f ⊗ 𝟙_{1}) ≫ rightUnitor Y = rightUnitor X ≫ f`. -/
theorem rightUnitor_naturality {X Y : Nat} (f : StochasticMatrix X Y) :
    (StochasticMatrix.kron f (idMatrix 1)).comp (rightUnitor Y)
    = (rightUnitor X).comp f := by
  apply StochasticMatrix.ext
  intro i j
  -- j : Fin Y gives 0 < Y, needed for Fin.second_pair on Fin (Y * 1).
  have hY : 0 < Y := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  show Fin.sumRat (fun k : Fin (Y * 1) =>
        (f.entry (Fin.first i) (Fin.first k)
          * kron (Fin.second i) (Fin.second k))
        * kron (Fin.first k) j)
     = Fin.sumRat (fun k : Fin X => kron (Fin.first i) k * f.entry k j)
  -- RHS collapses to f.entry (Fin.first i) j via sumRat_kron_mul.
  rw [sumRat_kron_mul (Fin.first i) (fun k : Fin X => f.entry k j)]
  -- Expand LHS via sumRat_unpair on Fin (Y * 1).
  rw [Fin.sumRat_unpair Y 1 _]
  rw [show (fun a : Fin Y => Fin.sumRat (fun b : Fin 1 =>
              (f.entry (Fin.first i) (Fin.first (Fin.pair a b))
                * kron (Fin.second i) (Fin.second (Fin.pair a b)))
              * kron (Fin.first (Fin.pair a b)) j))
      = (fun a : Fin Y => Fin.sumRat (fun b : Fin 1 =>
              (f.entry (Fin.first i) a * kron (Fin.second i) b)
              * kron a j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [Fin.first_pair a b, Fin.second_pair hY a b]))]
  -- Collapse the trivial Fin 1 factor using kron_fin_one.
  rw [show (fun a : Fin Y => Fin.sumRat (fun b : Fin 1 =>
              (f.entry (Fin.first i) a * kron (Fin.second i) b)
              * kron a j))
      = (fun a : Fin Y => Fin.sumRat (fun _ : Fin 1 =>
              f.entry (Fin.first i) a * kron a j)) from
      funext (fun a => Fin.sumRat_congr (fun b => by
        rw [kron_fin_one (Fin.second i) b, Rat.mul_one]))]
  -- Inner Fin 1 sums collapse pointwise.
  rw [show (fun a : Fin Y => Fin.sumRat (fun _ : Fin 1 =>
              f.entry (Fin.first i) a * kron a j))
      = (fun a : Fin Y => f.entry (Fin.first i) a * kron a j) from
      funext (fun a => Fin.sumRat_fin_one _)]
  -- Outer sum collapses via sumRat_mul_kron.
  exact sumRat_mul_kron j (fun a : Fin Y => f.entry (Fin.first i) a)

/-! ## Associator

  The associator `((X ⊗ Y) ⊗ Z) → (X ⊗ (Y ⊗ Z))` re-brackets the triple
  product.  Both source and target have the same underlying `Fin.val`
  encoding: `((a, b), c)` and `(a, (b, c))` both compute to
  `(X * Y) * c.val + X * b.val + a.val`.  So the associator is the
  "val-preserving" reindexing along the equation `(X*Y)*Z = X*(Y*Z)`. -/

/-- Re-index `Fin ((X*Y)*Z)` to `Fin (X*(Y*Z))` by preserving `val`. -/
def associatorFin {X Y Z : Nat} (i : Fin ((X * Y) * Z))
    : Fin (X * (Y * Z)) :=
  ⟨i.val, by rw [← Nat.mul_assoc]; exact i.isLt⟩

/-- Re-index `Fin (X*(Y*Z))` to `Fin ((X*Y)*Z)` by preserving `val`. -/
def associatorInvFin {X Y Z : Nat} (i : Fin (X * (Y * Z)))
    : Fin ((X * Y) * Z) :=
  ⟨i.val, by rw [Nat.mul_assoc]; exact i.isLt⟩

@[simp] theorem associatorFin_val {X Y Z : Nat} (i : Fin ((X * Y) * Z)) :
    (associatorFin i).val = i.val := rfl

@[simp] theorem associatorInvFin_val {X Y Z : Nat} (i : Fin (X * (Y * Z))) :
    (associatorInvFin i).val = i.val := rfl

/-- Round trip: `associatorInvFin ∘ associatorFin = id`. -/
theorem associatorInvFin_associatorFin {X Y Z : Nat}
    (i : Fin ((X * Y) * Z)) : associatorInvFin (associatorFin i) = i := by
  apply Fin.ext
  rfl

/-- Round trip: `associatorFin ∘ associatorInvFin = id`. -/
theorem associatorFin_associatorInvFin {X Y Z : Nat}
    (j : Fin (X * (Y * Z))) : associatorFin (associatorInvFin j) = j := by
  apply Fin.ext
  rfl

/-- The associator as a stochastic matrix.  Sends `i : Fin ((X*Y)*Z)`
    deterministically to its image under the val-preserving bijection
    `Fin ((X*Y)*Z) ≃ Fin (X*(Y*Z))`. -/
def associator (X Y Z : Nat) : StochasticMatrix ((X * Y) * Z) (X * (Y * Z)) where
  entry i j := kron (associatorFin i) j
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := sumRat_kron_eq_one (associatorFin i)

/-- The inverse associator. -/
def associatorInv (X Y Z : Nat) : StochasticMatrix (X * (Y * Z)) ((X * Y) * Z) where
  entry i j := kron (associatorInvFin i) j
  nonneg _ _ := kron_nonneg _ _
  row_sum_one i := sumRat_kron_eq_one (associatorInvFin i)

/-- `associator ≫ associatorInv = 𝟙_{(X*Y)*Z}`. -/
theorem associator_hom_inv (X Y Z : Nat) :
    (associator X Y Z).comp (associatorInv X Y Z) = idMatrix ((X * Y) * Z) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin (X * (Y * Z)) =>
        kron (associatorFin i) k * kron (associatorInvFin k) j)
     = kron i j
  rw [sumRat_kron_mul (associatorFin i)
        (fun k : Fin (X * (Y * Z)) => kron (associatorInvFin k) j)]
  rw [associatorInvFin_associatorFin]

/-- `associatorInv ≫ associator = 𝟙_{X*(Y*Z)}`. -/
theorem associator_inv_hom (X Y Z : Nat) :
    (associatorInv X Y Z).comp (associator X Y Z) = idMatrix (X * (Y * Z)) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin ((X * Y) * Z) =>
        kron (associatorInvFin i) k * kron (associatorFin k) j)
     = kron i j
  rw [sumRat_kron_mul (associatorInvFin i)
        (fun k : Fin ((X * Y) * Z) => kron (associatorFin k) j)]
  rw [associatorFin_associatorInvFin]

/-- `associatorFin` pushed past a triple `pair (pair a b) c`. -/
theorem associatorFin_pair {X Y Z : Nat}
    (a : Fin X) (b : Fin Y) (c : Fin Z) :
    associatorFin (Fin.pair (Fin.pair a b) c) = Fin.pair a (Fin.pair b c) := by
  apply Fin.ext
  show (X * Y) * c.val + (X * b.val + a.val)
       = X * (Y * c.val + b.val) + a.val
  rw [Nat.mul_add]
  rw [← Nat.mul_assoc]
  rw [← Nat.add_assoc]

/-- `associatorInvFin` pushed past a triple `pair a (pair b c)`. -/
theorem associatorInvFin_pair {X Y Z : Nat}
    (a : Fin X) (b : Fin Y) (c : Fin Z) :
    associatorInvFin (Fin.pair a (Fin.pair b c)) = Fin.pair (Fin.pair a b) c := by
  apply Fin.ext
  show X * (Y * c.val + b.val) + a.val
       = (X * Y) * c.val + (X * b.val + a.val)
  rw [Nat.mul_add]
  rw [← Nat.mul_assoc]
  rw [← Nat.add_assoc]

/-! ## Projection consistency through the associator

  `associatorFin` and `associatorInvFin` are val-preserving, so the
  iterated `Fin.first` / `Fin.second` projections commute with them
  in the way one expects: the triple `(a, b, c)` is recovered the same
  way from either bracketing.  The six lemmas below are val-level
  identities that follow from `Nat.mod_mod_of_dvd`,
  `Nat.div_div_eq_div_mul`, and one `omega` invocation for the mixed
  `div`/`mod` identity. -/

/-- Mixed div/mod identity: `(n / X) % Y = (n % (X * Y)) / X`. -/
private theorem Nat.div_mod_eq_mod_mul_div (n X Y : Nat) :
    (n / X) % Y = (n % (X * Y)) / X :=
  (Nat.mod_mul_right_div_self n X Y).symm

/-- `Fin.first ∘ associatorFin = Fin.first ∘ Fin.first`. -/
theorem first_associatorFin {X Y Z : Nat} (i : Fin ((X * Y) * Z)) :
    Fin.first (associatorFin i) = Fin.first (Fin.first i) := by
  apply Fin.ext
  show i.val % X = (i.val % (X * Y)) % X
  rw [Nat.mod_mod_of_dvd i.val (Nat.dvd_mul_right X Y)]

/-- `Fin.first ∘ Fin.second ∘ associatorFin = Fin.second ∘ Fin.first`. -/
theorem first_second_associatorFin {X Y Z : Nat} (i : Fin ((X * Y) * Z)) :
    Fin.first (Fin.second (associatorFin i)) = Fin.second (Fin.first i) := by
  apply Fin.ext
  show (i.val / X) % Y = (i.val % (X * Y)) / X
  exact Nat.div_mod_eq_mod_mul_div i.val X Y

/-- `Fin.second ∘ Fin.second ∘ associatorFin = Fin.second`. -/
theorem second_second_associatorFin {X Y Z : Nat} (i : Fin ((X * Y) * Z)) :
    Fin.second (Fin.second (associatorFin i)) = Fin.second i := by
  apply Fin.ext
  show (i.val / X) / Y = i.val / (X * Y)
  rw [Nat.div_div_eq_div_mul]

/-- `Fin.first ∘ Fin.first ∘ associatorInvFin = Fin.first`. -/
theorem first_first_associatorInvFin {X Y Z : Nat} (j : Fin (X * (Y * Z))) :
    Fin.first (Fin.first (associatorInvFin j)) = Fin.first j := by
  apply Fin.ext
  show (j.val % (X * Y)) % X = j.val % X
  rw [Nat.mod_mod_of_dvd j.val (Nat.dvd_mul_right X Y)]

/-- `Fin.second ∘ Fin.first ∘ associatorInvFin = Fin.first ∘ Fin.second`. -/
theorem second_first_associatorInvFin {X Y Z : Nat} (j : Fin (X * (Y * Z))) :
    Fin.second (Fin.first (associatorInvFin j)) = Fin.first (Fin.second j) := by
  apply Fin.ext
  show (j.val % (X * Y)) / X = (j.val / X) % Y
  exact (Nat.div_mod_eq_mod_mul_div j.val X Y).symm

/-- `Fin.second ∘ associatorInvFin = Fin.second ∘ Fin.second`. -/
theorem second_associatorInvFin {X Y Z : Nat} (j : Fin (X * (Y * Z))) :
    Fin.second (associatorInvFin j) = Fin.second (Fin.second j) := by
  apply Fin.ext
  show j.val / (X * Y) = (j.val / X) / Y
  rw [Nat.div_div_eq_div_mul]

/-! ## Associator naturality

  With the projection lemmas in hand, the associator naturality
  square reduces to two `sumRat_kron_mul` / `sumRat_mul_kron`
  applications plus six projection rewrites plus one `Rat.mul_assoc`. -/

/-- Flip a Kronecker delta past the associator reindexing: the val
    equation `(associatorFin k).val = k.val = (associatorInvFin j).val`
    makes both forms agree. -/
private theorem kron_associatorFin {X Y Z : Nat}
    (k : Fin ((X * Y) * Z)) (j : Fin (X * (Y * Z))) :
    kron (associatorFin k) j = kron k (associatorInvFin j) := by
  have h : associatorFin k = j ↔ k = associatorInvFin j := by
    constructor
    · intro hkj
      apply Fin.ext
      have hVal := congrArg Fin.val hkj
      rw [associatorFin_val] at hVal
      show k.val = (associatorInvFin j).val
      rw [associatorInvFin_val]
      exact hVal
    · intro hkj
      apply Fin.ext
      have hVal := congrArg Fin.val hkj
      rw [associatorInvFin_val] at hVal
      show (associatorFin k).val = j.val
      rw [associatorFin_val]
      exact hVal
  unfold kron
  by_cases hEq : associatorFin k = j
  · rw [if_pos hEq, if_pos (h.mp hEq)]
  · rw [if_neg hEq, if_neg (fun hk => hEq (h.mpr hk))]

/-- Associator naturality:
    `((f ⊗ g) ⊗ h) ≫ α = α ≫ (f ⊗ (g ⊗ h))`. -/
theorem associator_naturality {X Y Z X' Y' Z' : Nat}
    (f : StochasticMatrix X X')
    (g : StochasticMatrix Y Y')
    (h : StochasticMatrix Z Z') :
    (StochasticMatrix.kron (StochasticMatrix.kron f g) h).comp (associator X' Y' Z')
    = (associator X Y Z).comp
        (StochasticMatrix.kron f (StochasticMatrix.kron g h)) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin ((X' * Y') * Z') =>
        (StochasticMatrix.kron (StochasticMatrix.kron f g) h).entry i k
        * kron (associatorFin k) j)
     = Fin.sumRat (fun k : Fin (X * (Y * Z)) =>
        kron (associatorFin i) k
        * (StochasticMatrix.kron f (StochasticMatrix.kron g h)).entry k j)
  -- Flip the LHS kron via kron_associatorFin.
  rw [show (fun k : Fin ((X' * Y') * Z') =>
        (StochasticMatrix.kron (StochasticMatrix.kron f g) h).entry i k
        * kron (associatorFin k) j)
      = (fun k : Fin ((X' * Y') * Z') =>
        (StochasticMatrix.kron (StochasticMatrix.kron f g) h).entry i k
        * kron k (associatorInvFin j)) from
      funext (fun k => by rw [kron_associatorFin k j])]
  -- Pick the unique k on LHS via sumRat_mul_kron.
  rw [sumRat_mul_kron (associatorInvFin j)
      (fun k => (StochasticMatrix.kron (StochasticMatrix.kron f g) h).entry i k)]
  -- Pick the unique k on RHS via sumRat_kron_mul.
  rw [sumRat_kron_mul (associatorFin i)
      (fun k => (StochasticMatrix.kron f (StochasticMatrix.kron g h)).entry k j)]
  -- After unfolding kron entries, this is a triple-product equality
  -- modulo associator projections and Rat.mul_assoc.
  show (f.entry (Fin.first (Fin.first i)) (Fin.first (Fin.first (associatorInvFin j)))
        * g.entry (Fin.second (Fin.first i)) (Fin.second (Fin.first (associatorInvFin j))))
       * h.entry (Fin.second i) (Fin.second (associatorInvFin j))
     = f.entry (Fin.first (associatorFin i)) (Fin.first j)
       * (g.entry (Fin.first (Fin.second (associatorFin i))) (Fin.first (Fin.second j))
          * h.entry (Fin.second (Fin.second (associatorFin i))) (Fin.second (Fin.second j)))
  rw [first_first_associatorInvFin, second_first_associatorInvFin,
      second_associatorInvFin]
  rw [first_associatorFin, first_second_associatorFin,
      second_second_associatorFin]
  exact Rat.mul_assoc _ _ _

/-! ## Deterministic kernels

  Every val-preserving reindexing on FinStoch (the identity, the
  associator, the unitors) is a "deterministic kernel": its entry
  at `(i, j)` is the Kronecker delta on `(φ i, j)` for some
  underlying function `φ : Fin m → Fin n`.  Compositions and
  Kronecker products of deterministic kernels are again
  deterministic kernels, which collapses pentagon and triangle
  coherence to underlying-function equalities. -/

/-- The deterministic stochastic kernel induced by a function
    `φ : Fin m → Fin n`: send each row `i` to the unique column
    `φ i` with mass `1`. -/
def detMatrix {m n : Nat} (φ : Fin m → Fin n) : StochasticMatrix m n where
  entry i j := kron (φ i) j
  nonneg i j := kron_nonneg (φ i) j
  row_sum_one i := sumRat_kron_eq_one (φ i)

@[simp] theorem detMatrix_entry {m n : Nat} (φ : Fin m → Fin n)
    (i : Fin m) (j : Fin n) :
    (detMatrix φ).entry i j = kron (φ i) j := rfl

/-- Composition of deterministic kernels is the kernel of the
    composed function: `detMatrix φ ≫ detMatrix ψ = detMatrix (ψ ∘ φ)`. -/
theorem detMatrix_comp {m n p : Nat}
    (φ : Fin m → Fin n) (ψ : Fin n → Fin p) :
    (detMatrix φ).comp (detMatrix ψ) = detMatrix (fun i => ψ (φ i)) := by
  apply StochasticMatrix.ext
  intro i j
  show Fin.sumRat (fun k : Fin n => kron (φ i) k * kron (ψ k) j) = kron (ψ (φ i)) j
  exact sumRat_kron_mul (φ i) (fun k : Fin n => kron (ψ k) j)

/-- `idMatrix n = detMatrix id`: the identity kernel sends `i` to itself. -/
theorem idMatrix_eq_detMatrix (n : Nat) :
    idMatrix n = detMatrix (fun i : Fin n => i) := rfl

/-- `associator X Y Z = detMatrix associatorFin`. -/
theorem associator_eq_detMatrix (X Y Z : Nat) :
    associator X Y Z = detMatrix (@associatorFin X Y Z) := rfl

/-- `associatorInv X Y Z = detMatrix associatorInvFin`. -/
theorem associatorInv_eq_detMatrix (X Y Z : Nat) :
    associatorInv X Y Z = detMatrix (@associatorInvFin X Y Z) := rfl

/-- For `y : Fin (b * d)` with `0 < b`, the pair `(a, c)` equals `y`
    iff its components match `y`'s projections. -/
private theorem Fin.pair_eq_iff {b d : Nat} (hb : 0 < b)
    (a : Fin b) (c : Fin d) (y : Fin (b * d)) :
    Fin.pair a c = y ↔ a = Fin.first y ∧ c = Fin.second y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg Fin.first h
      rw [Fin.first_pair] at this
      exact this
    · have := congrArg Fin.second h
      rw [Fin.second_pair hb] at this
      exact this
  · intro ⟨h1, h2⟩
    rw [h1, h2]
    exact Fin.pair_first_second y

/-- Kronecker product of two deterministic kernels is the
    deterministic kernel of the paired function. -/
theorem kron_detMatrix {a b c d : Nat}
    (φ : Fin a → Fin b) (ψ : Fin c → Fin d) :
    StochasticMatrix.kron (detMatrix φ) (detMatrix ψ)
    = detMatrix (fun x : Fin (a * c) =>
        Fin.pair (φ (Fin.first x)) (ψ (Fin.second x))) := by
  apply StochasticMatrix.ext
  intro x y
  show kron (φ (Fin.first x)) (Fin.first y)
       * kron (ψ (Fin.second x)) (Fin.second y)
     = kron (Fin.pair (φ (Fin.first x)) (ψ (Fin.second x))) y
  have hbd : 0 < b * d := Nat.lt_of_le_of_lt (Nat.zero_le _) y.isLt
  have hb : 0 < b := Nat.pos_of_mul_pos_right hbd
  unfold kron
  by_cases hPair : Fin.pair (φ (Fin.first x)) (ψ (Fin.second x)) = y
  · have ⟨hF, hS⟩ := (Fin.pair_eq_iff hb _ _ y).mp hPair
    rw [if_pos hF, if_pos hS, if_pos hPair, Rat.one_mul]
  · rw [if_neg hPair]
    by_cases hF : φ (Fin.first x) = Fin.first y
    · have hS : ψ (Fin.second x) ≠ Fin.second y :=
        fun h => hPair ((Fin.pair_eq_iff hb _ _ y).mpr ⟨hF, h⟩)
      rw [if_pos hF, if_neg hS, Rat.mul_zero]
    · rw [if_neg hF, Rat.zero_mul]

/-- `leftUnitor Y = detMatrix Fin.second` (with `Fin.second : Fin (1 * Y) → Fin Y`). -/
theorem leftUnitor_eq_detMatrix (Y : Nat) :
    leftUnitor Y = detMatrix (fun i : Fin (1 * Y) => Fin.second i) := rfl

/-- `rightUnitor X = detMatrix Fin.first` (with `Fin.first : Fin (X * 1) → Fin X`). -/
theorem rightUnitor_eq_detMatrix (X : Nat) :
    rightUnitor X = detMatrix (fun i : Fin (X * 1) => Fin.first i) := rfl

/-- Pentagon coherence for the FinStoch associator. -/
theorem pentagon_FinStoch (W X Y Z : Nat) :
    (StochasticMatrix.kron (associator W X Y) (idMatrix Z)).comp
        ((associator W (X*Y) Z).comp
          (StochasticMatrix.kron (idMatrix W) (associator X Y Z)))
    = (associator (W*X) Y Z).comp (associator W X (Y*Z)) := by
  rw [associator_eq_detMatrix W X Y, idMatrix_eq_detMatrix Z, kron_detMatrix]
  rw [associator_eq_detMatrix W (X*Y) Z]
  rw [idMatrix_eq_detMatrix W, associator_eq_detMatrix X Y Z, kron_detMatrix]
  rw [associator_eq_detMatrix (W*X) Y Z, associator_eq_detMatrix W X (Y*Z)]
  rw [detMatrix_comp, detMatrix_comp, detMatrix_comp]
  congr 1
  funext x
  apply Fin.ext
  simp only [Fin.pair_val, Fin.first_val, Fin.second_val, associatorFin_val,
             Nat.div_add_mod]
  rw [← Nat.mul_assoc W X Y]
  exact Nat.div_add_mod x.val ((W*X)*Y)

/-- Helper Nat lemma for the triangle proof: closing the `X * 1` /
    `X` discrepancy in the two sides without triggering the motive
    problem with `i`'s type. -/
private theorem Nat.triangle_aux (n X : Nat) :
    X * (n / X) + n % X = X * (n / (X * 1)) + n % (X * 1) % X := by
  rw [Nat.mul_one]
  rw [Nat.mod_mod_of_dvd n (Nat.dvd_refl X)]

/-- Triangle coherence for the FinStoch associator and unitors:
    `α_{X, 1, Y} ≫ (id_X ⊗ leftUnitor Y) = rightUnitor X ⊗ id_Y`. -/
theorem triangle_FinStoch (X Y : Nat) :
    (associator X 1 Y).comp
        (StochasticMatrix.kron (idMatrix X) (leftUnitor Y))
    = StochasticMatrix.kron (rightUnitor X) (idMatrix Y) := by
  rw [associator_eq_detMatrix X 1 Y]
  rw [idMatrix_eq_detMatrix X, leftUnitor_eq_detMatrix Y, kron_detMatrix]
  rw [rightUnitor_eq_detMatrix X, idMatrix_eq_detMatrix Y, kron_detMatrix]
  rw [detMatrix_comp]
  congr 1
  funext i
  apply Fin.ext
  simp only [Fin.pair_val, Fin.first_val, Fin.second_val,
             associatorFin_val, Nat.div_one]
  exact Nat.triangle_aux i.val X

end FinStoch
end MarkovCat
