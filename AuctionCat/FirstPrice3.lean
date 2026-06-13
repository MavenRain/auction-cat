import AuctionCat.Mechanism

/-!
# AuctionCat.FirstPrice3

Three-bidder first-price sealed-bid auction over `FinStoch`.

Concrete instantiation:

- Bid space  : `Fin X` for the chosen `X`.
- Per-bidder outcome  : `Fin 2 × Fin X`  (allocation in {0, 1}, price).
- Joint input  : `Fin (X * X * X)`.
- Joint output  : `Fin ((2 * X) * (2 * X) * (2 * X))`.

Same shape as `FirstPrice`, generalised from 2 to 3 bidders.
Tie-breaking goes to the lower-index bidder: bidder 1 wins ties with
2 and 3; bidder 2 wins ties with 3.  The winner pays own bid (no
reserve), losers pay 0.

This demonstrates the n-bidder pattern; mechanisms for n > 3 follow
by analogy with extra Fin projections.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for three-bidder
    first-price sealed-bid. -/
def fpsb3Fn (X : Nat) (i : Fin (X * X * X)) :
    Fin ((2 * X) * (2 * X) * (2 * X)) :=
  let hX2X : 0 < (X * X) * X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hXX : 0 < X * X := Nat.pos_of_mul_pos_right hX2X
  let hX  : 0 < X     := Nat.pos_of_mul_pos_right hXX
  let b1  := Fin.first (Fin.first i)
  let b2  := Fin.second (Fin.first i)
  let b3  := Fin.second i
  let win1 := b1.val ≥ b2.val ∧ b1.val ≥ b3.val
  let win2 := ¬win1 ∧ b2.val ≥ b3.val
  let win3 := ¬win1 ∧ ¬win2
  let a1 : Fin 2 := if win1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if win2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a3 : Fin 2 := if win3 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let p1 : Fin X := if win1 then b1 else ⟨0, hX⟩
  let p2 : Fin X := if win2 then b2 else ⟨0, hX⟩
  let p3 : Fin X := if win3 then b3 else ⟨0, hX⟩
  Fin.pair (Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)) (Fin.pair a3 p3)

/-- The first-price sealed-bid mechanism over `FinStoch` for three
    bidders with bid space `Fin X`. -/
def firstPriceSealedBid3 (X : Nat) :
    StochasticMatrix (X * X * X) ((2 * X) * (2 * X) * (2 * X)) :=
  detMatrix (fpsb3Fn X)

/-- Bidder 1's truncated utility in a 3-bidder first-price sealed-bid
    auction, given valuation `v`, own bid `b1`, and opponent bids
    `b2`, `b3`.  Same tie-break as `fpsb3Fn` (bidder 1 wins iff
    `b1 ≥ b2 ∧ b1 ≥ b3`).  When b1 wins, utility = `v - b1` (Nat
    monus); else utility = 0. -/
def fpsbUtility3 (n : Nat) (v b1 b2 b3 : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ b3.val then
    ⟨v.val - b1.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Pointwise utility of truthful bidder 1 in 3-bidder fpsb is always
    zero: under `b1 = v`, the winner pays own bid = own valuation. -/
theorem fpsb3_utility_truthful_val_eq_zero (n : Nat) (v b2 b3 : Fin n) :
    (fpsbUtility3 n v v b2 b3).val = 0 := by
  unfold fpsbUtility3
  by_cases h : v.val ≥ b2.val ∧ v.val ≥ b3.val
  · simp [h]
  · simp [h]

/-- Bidder 1's truncated utility in a 3-bidder fpsb-with-reserve
    auction.  Same tie-break as `fpsb3ReserveFn`: b1 wins iff
    `b1 ≥ b2 ∧ b1 ≥ b3 ∧ b1 ≥ r`.  Utility = `v - b1` (Nat monus) on
    win, else 0. -/
def fpsbReserveUtility3 (n : Nat) (r v b1 b2 b3 : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ r.val then
    ⟨v.val - b1.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 1 gets zero utility in 3-bidder
    fpsb-with-reserve at every valuation profile and reserve. -/
theorem fpsb3Reserve_utility_truthful_val_eq_zero (n : Nat)
    (r v b2 b3 : Fin n) :
    (fpsbReserveUtility3 n r v v b2 b3).val = 0 := by
  unfold fpsbReserveUtility3
  by_cases h : v.val ≥ b2.val ∧ v.val ≥ b3.val ∧ v.val ≥ r.val
  · simp [h]
  · simp [h]

end AuctionCat
