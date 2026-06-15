import AuctionCat.Mechanism

/-!
# AuctionCat.SecondPrice3

Three-bidder second-price sealed-bid (Vickrey) auction over `FinStoch`.

Concrete instantiation:

- Bid space  : `Fin X` for the chosen `X`.
- Per-bidder outcome  : `Fin 2 × Fin X`  (allocation in {0, 1}, price).
- Joint input  : `Fin (X * X * X)`.
- Joint output  : `Fin ((2 * X) * (2 * X) * (2 * X))`.

Same shape as `SecondPrice`, generalised from 2 to 3 bidders.
Allocation: highest bid wins, ties to the lower-index bidder
(1 beats 2 beats 3).  Pricing (Vickrey rule): winner pays the max
of the OTHER bidders' bids; losers pay 0.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for three-bidder
    second-price sealed-bid (Vickrey). -/
def spsb3Fn (X : Nat) (i : Fin (X * X * X)) :
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
  -- Vickrey rule for n ≥ 2 bidders: winner pays max of OTHERS' bids.
  let p1 : Fin X :=
    if win1 then ⟨max b2.val b3.val, by
      have := b2.isLt; have := b3.isLt; omega⟩
    else ⟨0, hX⟩
  let p2 : Fin X :=
    if win2 then ⟨max b1.val b3.val, by
      have := b1.isLt; have := b3.isLt; omega⟩
    else ⟨0, hX⟩
  let p3 : Fin X :=
    if win3 then ⟨max b1.val b2.val, by
      have := b1.isLt; have := b2.isLt; omega⟩
    else ⟨0, hX⟩
  Fin.pair (Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)) (Fin.pair a3 p3)

/-- The second-price sealed-bid (Vickrey) mechanism over `FinStoch`
    for three bidders with bid space `Fin X`. -/
def secondPriceSealedBid3 (X : Nat) :
    StochasticMatrix (X * X * X) ((2 * X) * (2 * X) * (2 * X)) :=
  detMatrix (spsb3Fn X)

/-- **Allocation efficiency** of 3-bidder spsb.  Bidder 1 is allocated
    the item iff `b1 ≥ b2 ∧ b1 ≥ b3` (weak ≥ on both — bidder 1 wins
    ties). -/
theorem spsb3_bidder1_allocated_iff_winner (n : Nat) (i : Fin (n * n * n)) :
    (Fin.first (Fin.first (Fin.first (spsb3Fn n i)))).val = 1
    ↔ (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val := by
  have hnnn : 0 < n * n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsb3Fn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : i.val % (n * n) / n ≤ i.val % n
              ∧ i.val / (n * n) ≤ i.val % n
  · simp [h]
  · simp [h]


end AuctionCat
