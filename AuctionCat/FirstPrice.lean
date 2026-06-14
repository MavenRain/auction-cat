import AuctionCat.Mechanism

/-!
# AuctionCat.FirstPrice

First-price sealed-bid auction for two bidders over `FinStoch`.

Concrete instantiation:

- Bid space  : `Fin n` for the chosen `n`.
- Per-bidder outcome  : `Fin 2 × Fin n`  (allocation in {0, 1}, price).
- Joint input  : `Fin (n * n)`.
- Joint output  : `Fin ((2 * n) * (2 * n))`.

The mechanism is a deterministic kernel (a `detMatrix`):

  fpsbFn n (i : Fin (n * n)) : Fin ((2 * n) * (2 * n))
    decodes  i ↦ (b₁, b₂)
    allocates  bidder 1 wins iff  b₁ ≥ b₂   (ties to bidder 1)
    prices    winner pays own bid; loser pays 0
    encodes the four outcome components back.

Tie-breaking convention favours bidder 1, matching the standard
first-price specification.  Loser pays 0.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for two-bidder
    first-price sealed-bid. -/
def fpsbFn (n : Nat) (i : Fin (n * n)) : Fin ((2 * n) * (2 * n)) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_left hnn
  let b1  := Fin.first i
  let b2  := Fin.second i
  let a1 : Fin 2 := if b1.val ≥ b2.val then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if b1.val ≥ b2.val then ⟨0, by decide⟩ else ⟨1, by decide⟩
  let p1 : Fin n := if b1.val ≥ b2.val then b1 else ⟨0, hn⟩
  let p2 : Fin n := if b1.val ≥ b2.val then ⟨0, hn⟩ else b2
  Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)

/-- The first-price sealed-bid mechanism over `FinStoch` for two
    bidders with bid space `Fin n`. -/
def firstPriceSealedBid (n : Nat) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  detMatrix (fpsbFn n)

/-- **Allocation rule** of fpsb.  Bidder 1 is allocated the item iff
    bidder 1's bid is at least bidder 2's (tiebreak to bidder 1).
    Same allocation rule as spsb — the two formats differ only in
    pricing. -/
theorem fpsb_bidder1_allocated_iff_higher_bid (n : Nat) (i : Fin (n * n)) :
    (Fin.first (Fin.first (fpsbFn n i))).val = 1
    ↔ (Fin.first i).val ≥ (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
  · simp [h]
  · simp [h]

/-- Bidder 2's fpsb allocation: bidder 2 wins iff `b1 < b2` (strict —
    ties go to bidder 1).  Same allocation rule as spsb. -/
theorem fpsb_bidder2_allocated_iff_strict_higher_bid (n : Nat)
    (i : Fin (n * n)) :
    (Fin.first (Fin.second (fpsbFn n i))).val = 1
    ↔ (Fin.first i).val < (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
  · simp [h]; omega
  · simp [h]; omega

/-- **Exactly one winner** in fpsb: bidder 1's allocation and
    bidder 2's allocation sum to `1` at every joint bid.  Captures
    the single-item-auction property. -/
theorem fpsb_exactly_one_winner (n : Nat) (i : Fin (n * n)) :
    (Fin.first (Fin.first (fpsbFn n i))).val
    + (Fin.first (Fin.second (fpsbFn n i))).val = 1 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
  · simp [h]
  · simp [h]


/-! ## Truthful play under fpsb

  Under truthful bidding, every bidder either loses (utility = 0) or
  wins and pays their own bid = their own valuation, so utility =
  v - v = 0.  The closed-form outcome is the constant zero-utility
  pair, regardless of valuations. -/

/-- The deterministic outcome of `fpsbAuction n` at any joint
    valuation under truthful bidding: both bidders get zero utility. -/
def fpsbAuctionFn (n : Nat) (v_joint : Fin (n * n)) : Fin (n * n) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_right hnn
  Fin.pair (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)

/-- Bidder 1's truncated utility in a 2-bidder first-price sealed-bid
    auction, given valuation `v`, own bid `b1`, and opponent bid `b2`.
    Same tie-break as `fpsbFn` (bidder 1 wins iff `b1 ≥ b2`).  When
    b1 wins, utility = `v - b1` (Nat monus, so over-bidding truncates
    to 0); when b1 loses, utility = 0. -/
def fpsbUtility (n : Nat) (v b1 b2 : Fin n) : Fin n :=
  if b1.val ≥ b2.val then
    ⟨v.val - b1.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- **Truthful bidding is NOT a dominant strategy in fpsb**.  Concrete
    counterexample: at `v = 1`, bidding `0` against `b2 = 0` strictly
    dominates truthful (bidding `1` against `b2 = 0`).

    Truthful yields utility `1 - 1 = 0`; the deviation `b1 = 0` wins
    by tie-break and pays `0`, yielding utility `1 - 0 = 1`.  Hence
    `fpsbUtility n 1 1 0 < fpsbUtility n 1 0 0` strictly. -/
theorem fpsb_truthful_not_dominant (n : Nat) (h2 : 2 ≤ n) :
    ∃ (v b1 b2 : Fin n),
      (fpsbUtility n v v b2).val < (fpsbUtility n v b1 b2).val := by
  refine ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ?_⟩
  unfold fpsbUtility
  simp

/-- Bidder 1's truncated utility in a 2-bidder fpsb-with-reserve
    auction, given reserve `r`, valuation `v`, own bid `b1`, and
    opponent bid `b2`.  Same tie-break as `fpsbReserveFn`.  When b1
    wins (b1 ≥ b2 ∧ b1 ≥ r), utility = `v - b1` (Nat monus); else 0. -/
def fpsbReserveUtility (n : Nat) (r v b1 b2 : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ r.val then
    ⟨v.val - b1.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 1 gets zero utility in fpsb-with-reserve at every
    valuation profile and reserve.  If they win, they pay own bid =
    own valuation; if they lose (either outbid or below reserve), 0. -/
theorem fpsbReserve_utility_truthful_val_eq_zero (n : Nat) (r v b2 : Fin n) :
    (fpsbReserveUtility n r v v b2).val = 0 := by
  unfold fpsbReserveUtility
  by_cases h : v.val ≥ b2.val ∧ v.val ≥ r.val
  · simp [h]
  · simp [h]

/-- **At maximal reserve `r = n - 1`, every fpsbReserve strategy
    yields zero utility for bidder 1**.  Reason: to win, bidder 1
    must bid ≥ n - 1, forcing `b1 = n - 1` (since bids live in
    `Fin n`); winning then yields `v - (n - 1) = 0` (Nat monus,
    since `v ≤ n - 1`).  Losing yields 0. -/
theorem fpsbReserve_utility_max_reserve_val_eq_zero (n : Nat) (hn : 0 < n)
    (v b1 b2 : Fin n) :
    (fpsbReserveUtility n ⟨n - 1, by omega⟩ v b1 b2).val = 0 := by
  unfold fpsbReserveUtility
  by_cases h : b1.val ≥ b2.val ∧ b1.val ≥ n - 1
  · simp [h]
    have hb1 := b1.isLt
    have hv := v.isLt
    omega
  · simp [h]

/-- Bidder 2's truncated utility in a 2-bidder first-price sealed-bid
    auction, given valuation `v`, opponent's bid `opp_bid`, and own
    bid `my_bid`.  Bidder 2 wins iff `my_bid > opp_bid` (strict — ties
    go to bidder 1, matching `fpsbFn`'s convention).  Utility:
    `v - my_bid` on win (Nat monus); 0 on loss. -/
def fpsbBidder2Util (n : Nat) (v opp_bid my_bid : Fin n) : Fin n :=
  if opp_bid.val < my_bid.val then
    ⟨v.val - my_bid.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 2 in fpsb gets zero utility regardless of opponent
    bid: winner pays own bid = own valuation; loser gets 0. -/
theorem fpsb_bidder2_utility_truthful_val_eq_zero (n : Nat)
    (v opp_bid : Fin n) :
    (fpsbBidder2Util n v opp_bid v).val = 0 := by
  unfold fpsbBidder2Util
  by_cases h : opp_bid.val < v.val
  · simp [h]
  · simp [h]

/-- Bidder 2's truncated utility in a 2-bidder fpsb-with-reserve
    auction.  Bidder 2 wins iff `my_bid > opp_bid` (strict tiebreak)
    AND `my_bid ≥ r`.  On win, utility = `v - my_bid` (Nat monus);
    else 0. -/
def fpsbReserveBidder2Util (n : Nat) (r v opp_bid my_bid : Fin n) : Fin n :=
  if opp_bid.val < my_bid.val ∧ my_bid.val ≥ r.val then
    ⟨v.val - my_bid.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Truthful bidder 2 in fpsb-with-reserve gets zero utility at every
    profile and reserve. -/
theorem fpsbReserve_bidder2_utility_truthful_val_eq_zero (n : Nat)
    (r v opp_bid : Fin n) :
    (fpsbReserveBidder2Util n r v opp_bid v).val = 0 := by
  unfold fpsbReserveBidder2Util
  by_cases h : opp_bid.val < v.val ∧ v.val ≥ r.val
  · simp [h]
  · simp [h]

/-- **At maximal reserve, bidder 2's fpsbReserve utility is also
    identically zero**, regardless of strategy.  Same argument as
    bidder 1: winning requires `my_bid ≥ r = n - 1`, so `my_bid =
    n - 1`; pay `n - 1`; util `v - (n - 1) = 0`. -/
theorem fpsbReserve_bidder2_utility_max_reserve_val_eq_zero (n : Nat)
    (hn : 0 < n) (v opp_bid my_bid : Fin n) :
    (fpsbReserveBidder2Util n ⟨n - 1, by omega⟩ v opp_bid my_bid).val = 0 := by
  unfold fpsbReserveBidder2Util
  by_cases h : opp_bid.val < my_bid.val ∧ my_bid.val ≥ n - 1
  · simp [h]
    have hmb := my_bid.isLt
    have hv := v.isLt
    omega
  · simp [h]

end AuctionCat
