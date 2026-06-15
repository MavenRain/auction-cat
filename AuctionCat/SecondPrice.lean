import AuctionCat.Mechanism

/-!
# AuctionCat.SecondPrice

Second-price sealed-bid (Vickrey) auction for two bidders over
`FinStoch`.

Same shape as `FirstPrice`: deterministic kernel decoding `(b₁, b₂)`,
allocating to the higher bidder (ties to bidder 1), encoding the
four outcome components.

The only difference from first-price is the pricing rule:

  first-price  : winner pays own bid
  second-price : winner pays the other bidder's bid

The loser still pays 0.

For two bidders this is equivalent to "winner pays the second-highest
bid", the standard Vickrey rule.  Strategic interest: bidding one's
true valuation is a (weakly) dominant strategy under this rule, a
theorem stated and proved later in the AuctionCat library.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for two-bidder
    second-price sealed-bid (Vickrey). -/
def spsbFn (n : Nat) (i : Fin (n * n)) : Fin ((2 * n) * (2 * n)) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_left hnn
  let b1  := Fin.first i
  let b2  := Fin.second i
  let a1 : Fin 2 := if b1.val ≥ b2.val then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if b1.val ≥ b2.val then ⟨0, by decide⟩ else ⟨1, by decide⟩
  -- Vickrey rule: winner pays the OTHER bid.
  let p1 : Fin n := if b1.val ≥ b2.val then b2 else ⟨0, hn⟩
  let p2 : Fin n := if b1.val ≥ b2.val then ⟨0, hn⟩ else b1
  Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)

/-- The second-price sealed-bid (Vickrey) mechanism over `FinStoch`
    for two bidders with bid space `Fin n`. -/
def secondPriceSealedBid (n : Nat) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  detMatrix (spsbFn n)

/-- **Allocation efficiency** of spsb under truthful play.  Bidder 1
    is allocated the item (`a1 = 1`) iff bidder 1's bid is at least
    bidder 2's (equivalently, under truthful, iff `v1 ≥ v2`).
    Tie-break favors bidder 1. -/
theorem spsb_bidder1_allocated_iff_higher_bid (n : Nat) (i : Fin (n * n)) :
    (Fin.first (Fin.first (spsbFn n i))).val = 1
    ↔ (Fin.first i).val ≥ (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : i.val / n ≤ i.val % n
  · simp [h]
  · simp [h]

/-- Bidder 2's allocation: bidder 2 wins iff bidder 1 strictly loses
    (`b1 < b2`) — ties go to bidder 1. -/
theorem spsb_bidder2_allocated_iff_strict_higher_bid (n : Nat)
    (i : Fin (n * n)) :
    (Fin.first (Fin.second (spsbFn n i))).val = 1
    ↔ (Fin.first i).val < (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : i.val / n ≤ i.val % n
  · simp [h]
  · simp [h]; omega

/-- **Exactly one winner** in spsb: bidder 1's allocation and
    bidder 2's allocation sum to `1` at every joint bid.  Captures
    the single-item-auction property. -/
theorem spsb_exactly_one_winner (n : Nat) (i : Fin (n * n)) :
    (Fin.first (Fin.first (spsbFn n i))).val
    + (Fin.first (Fin.second (spsbFn n i))).val = 1 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : i.val / n ≤ i.val % n
  · simp [h]
  · simp [h]

/-! ## Dominant-strategy truthfulness

  The Vickrey auction's central property: bidding one's valuation is
  a (weakly) dominant strategy.  We model bidder 1 facing bidder 2's
  bid `b2`; the theorem shows that, for any deviation bid `b1`,
  truthful bidding gives utility at least as high as the deviation. -/

/-- Bidder 2's truncated utility in a 2-bidder Vickrey auction given
    valuation `v`, opponent's bid `opp_bid`, and own bid `my_bid`.
    Bidder 2 wins iff `opp_bid < my_bid` (STRICT; ties go to bidder 1
    by the `b1 ≥ b2` rule in `spsbFn`); winner pays `opp_bid`. -/
def vickreyBidder2Util (n : Nat) (v opp_bid my_bid : Fin n) : Fin n :=
  if opp_bid.val < my_bid.val then
    ⟨v.val - opp_bid.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness from bidder 2's perspective:
    truthful bidding (`my_bid = v`) weakly dominates any deviation. -/
theorem vickrey_bidder2_truthful_dominant (n : Nat) (v opp_bid bid_val : Fin n) :
    (vickreyBidder2Util n v opp_bid v).val
    ≥ (vickreyBidder2Util n v opp_bid bid_val).val := by
  unfold vickreyBidder2Util
  by_cases h1 : opp_bid.val < v.val <;>
  by_cases h2 : opp_bid.val < bid_val.val <;>
  simp [h1, h2] <;>
  omega

/-- Bidder 1's truncated utility in a Vickrey auction, given
    valuation `v`, own bid `b1`, and bidder 2's bid `b2`. -/
def vickreyUtility (n : Nat) (v b1 b2 : Fin n) : Fin n :=
  if b1.val ≥ b2.val then
    ⟨v.val - b2.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness in second-price sealed-bid.

    For any valuation `v`, any deviation bid `b1`, and any opposing
    bid `b2`, bidding `v` truthfully yields utility at least as high
    as bidding `b1`. -/
theorem vickrey_truthful_dominant (n : Nat) (v b1 b2 : Fin n) :
    (vickreyUtility n v v b2).val ≥ (vickreyUtility n v b1 b2).val := by
  unfold vickreyUtility
  by_cases hv  : v.val ≥ b2.val <;>
  by_cases hb1 : b1.val ≥ b2.val <;>
  simp [hv, hb1] <;>
  omega

/-! ## Bidder-1 utility under a strategy

  Lifts the utility-level truthfulness theorem to the "bidder 1
  utility under strategy `bid` against truthful bidder 2" function,
  which is the bidder-1 component of the `spsbAuction` kernel's
  deterministic output at the valuation profile `(v1, v2)` when
  bidder 1 uses `bid` and bidder 2 is truthful. -/

/-- Bidder 1's utility in a 2-bidder Vickrey auction when bidder 1
    uses the strategy `bid` and bidder 2 bids truthfully. -/
def spsbBidder1Utility (n : Nat) (bid : Fin n → Fin n)
    (v1 v2 : Fin n) : Fin n :=
  vickreyUtility n v1 (bid v1) v2

/-- Truthfulness is dominant for bidder 1: bidding own valuation
    yields utility at least as high as any deviation strategy
    `bid`, against any opposing valuation `v2` (here played by a
    truthful bidder 2). -/
theorem spsb_bidder1_truthful_dominates
    (n : Nat) (bid : Fin n → Fin n) (v1 v2 : Fin n) :
    (spsbBidder1Utility n (fun v => v) v1 v2).val
    ≥ (spsbBidder1Utility n bid v1 v2).val := by
  unfold spsbBidder1Utility
  exact vickrey_truthful_dominant n v1 (bid v1) v2

end AuctionCat
