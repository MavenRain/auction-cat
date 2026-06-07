import AuctionCat.Reserve
import AuctionCat.SecondPrice3
import AuctionCat.Auction
import AuctionCat.Vickrey3
import AuctionCat.ReserveTruth

/-!
# AuctionCat.Reserve3Truth

Three-bidder reserve-price Vickrey truthfulness and open-game
pipeline connection.

Mirrors `AuctionCat.ReserveTruth` (two-bidder case) but for three
bidders.  Truthfulness still holds because the winner's payment
`max r (max of others' bids)` is independent of the winner's own
bid.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder's truncated utility in a three-bidder Vickrey-with-reserve
    auction.  Wins iff own bid `b1` is highest among the three and
    meets the reserve; pays `max r (max b2 b3)` on win. -/
def vickreyReserveUtility3 (n : Nat) (v b1 b2 b3 r : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ r.val then
    ⟨v.val - max r.val (max b2.val b3.val), by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness for three-bidder Vickrey with
    reserve. -/
theorem vickreyReserve3_truthful_dominant (n : Nat) (v b1 b2 b3 r : Fin n) :
    (vickreyReserveUtility3 n v v b2 b3 r).val
    ≥ (vickreyReserveUtility3 n v b1 b2 b3 r).val := by
  unfold vickreyReserveUtility3
  by_cases hv1 : v.val ≥ b2.val ∧ v.val ≥ b3.val ∧ v.val ≥ r.val <;>
  by_cases hb1 : b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ r.val <;>
  simp [hv1, hb1] <;>
  omega

/-! ## Closed-form deterministic outcome function -/

/-- Deterministic outcome of `spsb3ReserveAuction n r` at joint
    valuation `v_joint` (all bidders truthful). -/
def spsb3ReserveAuctionFn (n : Nat) (r : Fin n)
    (v_joint : Fin ((n * n) * n)) : Fin ((n * n) * n) :=
  let v1 := Fin.first (Fin.first v_joint)
  let v2 := Fin.second (Fin.first v_joint)
  let v3 := Fin.second v_joint
  Fin.pair
    (Fin.pair
      (vickreyReserveUtility3 n v1 v1 v2 v3 r)
      (vickreyReserveUtility3 n v2 v2 v1 v3 r))
    (vickreyReserveUtility3 n v3 v3 v1 v2 r)

/-- Deterministic outcome of a 3-bidder spsbReserve auction when
    bidder 1 deviates with strategy `bid` and bidders 2, 3 stay
    truthful. -/
def spsb3ReserveAuctionDeviator1Fn (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin ((n * n) * n)) :
    Fin ((n * n) * n) :=
  let v1 := Fin.first (Fin.first v_joint)
  let v2 := Fin.second (Fin.first v_joint)
  let v3 := Fin.second v_joint
  Fin.pair
    (Fin.pair
      (vickreyReserveUtility3 n v1 (bid v1) v2 v3 r)
      (vickreyReserveUtility3 n v2 v2 (bid v1) v3 r))
    (vickreyReserveUtility3 n v3 v3 (bid v1) v2 r)

/-- **Kernel-level three-bidder Vickrey-with-reserve truthfulness**:
    bidder 1's expected utility under truthful play weakly
    dominates the expected utility under any single-deviator
    variant, at the deterministic-outcome-function level. -/
theorem spsb3Reserve_bidder1_kernel_dominance (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin ((n * n) * n)) :
    auctionBidder1Util3 n
        (detMatrix (spsb3ReserveAuctionFn n r)) v_joint
    ≥ auctionBidder1Util3 n
        (detMatrix (spsb3ReserveAuctionDeviator1Fn n r bid)) v_joint := by
  rw [auctionBidder1Util3_det, auctionBidder1Util3_det]
  unfold spsb3ReserveAuctionFn spsb3ReserveAuctionDeviator1Fn
  rw [Fin.first_pair, Fin.first_pair, Fin.first_pair, Fin.first_pair]
  exact_mod_cast vickreyReserve3_truthful_dominant n
    (Fin.first (Fin.first v_joint))
    (bid (Fin.first (Fin.first v_joint)))
    (Fin.second (Fin.first v_joint))
    (Fin.second v_joint)
    r

end AuctionCat
