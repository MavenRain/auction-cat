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

/-- **At maximal reserve `r = n - 1`, every fpsb3Reserve strategy
    yields zero utility for bidder 1** (3 bidders).  Same argument
    as the 2-bidder case: to win, bidder 1 must bid n - 1; winning
    yields `v - (n - 1) = 0`. -/
theorem fpsb3Reserve_utility_max_reserve_val_eq_zero (n : Nat) (hn : 0 < n)
    (v b1 b2 b3 : Fin n) :
    (fpsbReserveUtility3 n ⟨n - 1, by omega⟩ v b1 b2 b3).val = 0 := by
  unfold fpsbReserveUtility3
  by_cases h : b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ n - 1
  · simp [h]
    have hb1 := b1.isLt
    have hv := v.isLt
    omega
  · simp [h]

/-- Bidder 2's truncated utility in a 3-bidder fpsb auction.  Bidder 2
    wins iff `opp_b1 < my_b2` (strict — tiebreak gives bidder 1
    priority) AND `my_b2 ≥ opp_b3` (weak — bidder 2 has priority over
    3); pays own bid on win. -/
def fpsbBidder2Util3 (n : Nat) (v opp_b1 my_b2 opp_b3 : Fin n) : Fin n :=
  if opp_b1.val < my_b2.val ∧ my_b2.val ≥ opp_b3.val then
    ⟨v.val - my_b2.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 2 in 3-bidder fpsb gets zero utility at every
    valuation profile. -/
theorem fpsb3_bidder2_utility_truthful_val_eq_zero (n : Nat)
    (v opp_b1 opp_b3 : Fin n) :
    (fpsbBidder2Util3 n v opp_b1 v opp_b3).val = 0 := by
  unfold fpsbBidder2Util3
  by_cases h : opp_b1.val < v.val ∧ v.val ≥ opp_b3.val
  · simp [h]
  · simp [h]

/-- Bidder 3's truncated utility in a 3-bidder fpsb auction.  Bidder 3
    wins iff both `opp_b1 < my_b3` AND `opp_b2 < my_b3` (strict on
    both — bidders 1 and 2 win ties).  Pays own bid on win. -/
def fpsbBidder3Util3 (n : Nat) (v opp_b1 opp_b2 my_b3 : Fin n) : Fin n :=
  if opp_b1.val < my_b3.val ∧ opp_b2.val < my_b3.val then
    ⟨v.val - my_b3.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 3 in 3-bidder fpsb gets zero utility at every
    valuation profile. -/
theorem fpsb3_bidder3_utility_truthful_val_eq_zero (n : Nat)
    (v opp_b1 opp_b2 : Fin n) :
    (fpsbBidder3Util3 n v opp_b1 opp_b2 v).val = 0 := by
  unfold fpsbBidder3Util3
  by_cases h : opp_b1.val < v.val ∧ opp_b2.val < v.val
  · simp [h]
  · simp [h]

/-- Bidder 2's truncated utility in 3-bidder fpsb-with-reserve.  Same
    tiebreak as no-reserve PLUS the reserve clearing condition. -/
def fpsbReserveBidder2Util3 (n : Nat)
    (r v opp_b1 my_b2 opp_b3 : Fin n) : Fin n :=
  if opp_b1.val < my_b2.val ∧ my_b2.val ≥ opp_b3.val ∧ my_b2.val ≥ r.val then
    ⟨v.val - my_b2.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 2 in 3-bidder fpsb-with-reserve gets zero utility
    at every profile and reserve. -/
theorem fpsb3Reserve_bidder2_utility_truthful_val_eq_zero (n : Nat)
    (r v opp_b1 opp_b3 : Fin n) :
    (fpsbReserveBidder2Util3 n r v opp_b1 v opp_b3).val = 0 := by
  unfold fpsbReserveBidder2Util3
  by_cases h :
      opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val
  · simp [h]
  · simp [h]

/-- Bidder 3's truncated utility in 3-bidder fpsb-with-reserve.  Same
    tiebreak as no-reserve PLUS the reserve clearing condition. -/
def fpsbReserveBidder3Util3 (n : Nat)
    (r v opp_b1 opp_b2 my_b3 : Fin n) : Fin n :=
  if opp_b1.val < my_b3.val ∧ opp_b2.val < my_b3.val ∧ my_b3.val ≥ r.val then
    ⟨v.val - my_b3.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 3 in 3-bidder fpsb-with-reserve gets zero utility
    at every profile and reserve. -/
theorem fpsb3Reserve_bidder3_utility_truthful_val_eq_zero (n : Nat)
    (r v opp_b1 opp_b2 : Fin n) :
    (fpsbReserveBidder3Util3 n r v opp_b1 opp_b2 v).val = 0 := by
  unfold fpsbReserveBidder3Util3
  by_cases h :
      opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val
  · simp [h]
  · simp [h]

end AuctionCat
