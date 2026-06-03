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

/-! ## Dominant-strategy truthfulness

  The Vickrey auction's central property: bidding one's valuation is
  a (weakly) dominant strategy.  We model bidder 1 facing bidder 2's
  bid `b2`; the theorem shows that, for any deviation bid `b1`,
  truthful bidding gives utility at least as high as the deviation. -/

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

end AuctionCat
