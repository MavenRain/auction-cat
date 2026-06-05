import AuctionCat.SecondPrice3
import AuctionCat.Auction
import AuctionCat.KernelTruth

/-!
# AuctionCat.Vickrey3

Three-bidder Vickrey truthfulness theorems, paralleling the two-bidder
versions in `AuctionCat.SecondPrice` and `AuctionCat.KernelTruth`.

Provides:

  - `vickreyUtility3`: bidder utility under three-bidder Vickrey.
  - `vickrey3_truthful_dominant`: weak dominance of truthful bidding.
  - `spsbBidder1Utility3` + `spsb3_bidder1_truthful_dominates`:
    lift to the auction-context bidder-1 utility function.
  - `auctionBidder1Util3`: kernel-level expected bidder-1 utility.
  - `spsbAuctionFn3` / `spsbAuctionDeviator1Fn3`: the deterministic
    outcome functions of the truthful and bidder-1-deviator
    three-bidder auctions.
  - `spsb3_bidder1_kernel_dominance`: kernel-level truthfulness
    (at the deterministic-function level).
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder's truncated utility in a three-bidder Vickrey auction
    given valuation `v`, own bid `b1`, and the other two bidders'
    bids `b2`, `b3`.

    Wins iff `b1 ≥ b2` and `b1 ≥ b3`; pays `max b2 b3` on win;
    pays 0 on loss. -/
def vickreyUtility3 (n : Nat) (v b1 b2 b3 : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ b3.val then
    ⟨v.val - max b2.val b3.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness for three-bidder Vickrey: for any
    valuation, any deviation bid, and any opposing bids, truthful
    bidding yields utility at least as high as the deviation. -/
theorem vickrey3_truthful_dominant (n : Nat) (v b1 b2 b3 : Fin n) :
    (vickreyUtility3 n v v b2 b3).val
    ≥ (vickreyUtility3 n v b1 b2 b3).val := by
  unfold vickreyUtility3
  by_cases hv1 : v.val ≥ b2.val ∧ v.val ≥ b3.val <;>
  by_cases hb1 : b1.val ≥ b2.val ∧ b1.val ≥ b3.val <;>
  simp [hv1, hb1] <;>
  omega

/-- Bidder 1's utility in a 3-bidder Vickrey auction when bidder 1
    uses strategy `bid` and bidders 2 and 3 bid truthfully. -/
def spsbBidder1Utility3 (n : Nat) (bid : Fin n → Fin n)
    (v1 v2 v3 : Fin n) : Fin n :=
  vickreyUtility3 n v1 (bid v1) v2 v3

/-- Truthfulness lifted to bidder 1's utility function for three
    bidders. -/
theorem spsb3_bidder1_truthful_dominates
    (n : Nat) (bid : Fin n → Fin n) (v1 v2 v3 : Fin n) :
    (spsbBidder1Utility3 n (fun v => v) v1 v2 v3).val
    ≥ (spsbBidder1Utility3 n bid v1 v2 v3).val := by
  unfold spsbBidder1Utility3
  exact vickrey3_truthful_dominant n v1 (bid v1) v2 v3

/-! ## Kernel-level lift -/

/-- Expected bidder-1 utility of any 3-bidder auction kernel. -/
def auctionBidder1Util3 (n : Nat)
    (auction : StochasticMatrix ((n * n) * n) ((n * n) * n))
    (v_joint : Fin ((n * n) * n)) : Rat :=
  Fin.sumRat (fun u_joint : Fin ((n * n) * n) =>
    auction.entry v_joint u_joint
    * ((Fin.first (Fin.first u_joint)).val : Nat).cast)

/-- For deterministic 3-bidder kernels, the expected bidder-1
    utility collapses via `sumRat_kron_mul`. -/
theorem auctionBidder1Util3_det (n : Nat)
    (f : Fin ((n * n) * n) → Fin ((n * n) * n))
    (v_joint : Fin ((n * n) * n)) :
    auctionBidder1Util3 n (detMatrix f) v_joint
    = ((Fin.first (Fin.first (f v_joint))).val : Nat).cast := by
  unfold auctionBidder1Util3
  show Fin.sumRat (fun u_joint : Fin ((n * n) * n) =>
        kron (f v_joint) u_joint
        * ((Fin.first (Fin.first u_joint)).val : Nat).cast)
      = ((Fin.first (Fin.first (f v_joint))).val : Nat).cast
  exact sumRat_kron_mul (f v_joint)
    (fun u : Fin ((n * n) * n) =>
      ((Fin.first (Fin.first u)).val : Nat).cast)

/-- The deterministic outcome of `spsb3Auction n` at joint valuation
    `(v1, v2, v3)` (all truthful): each bidder gets their Vickrey
    utility against the other two bidders' valuations. -/
def spsbAuctionFn3 (n : Nat) (v_joint : Fin ((n * n) * n)) :
    Fin ((n * n) * n) :=
  let v1 := Fin.first (Fin.first v_joint)
  let v2 := Fin.second (Fin.first v_joint)
  let v3 := Fin.second v_joint
  Fin.pair
    (Fin.pair
      (vickreyUtility3 n v1 v1 v2 v3)
      (vickreyUtility3 n v2 v2 v1 v3))
    (vickreyUtility3 n v3 v3 v1 v2)

/-- The deterministic outcome of a 3-bidder spsb auction when
    bidder 1 deviates with strategy `bid` and bidders 2, 3 stay
    truthful. -/
def spsbAuctionDeviator1Fn3 (n : Nat) (bid : Fin n → Fin n)
    (v_joint : Fin ((n * n) * n)) : Fin ((n * n) * n) :=
  let v1 := Fin.first (Fin.first v_joint)
  let v2 := Fin.second (Fin.first v_joint)
  let v3 := Fin.second v_joint
  Fin.pair
    (Fin.pair
      (vickreyUtility3 n v1 (bid v1) v2 v3)
      (vickreyUtility3 n v2 v2 (bid v1) v3))
    (vickreyUtility3 n v3 v3 (bid v1) v2)

/-- **Kernel-level three-bidder Vickrey truthfulness**: bidder 1's
    expected utility under truthful spsb3 weakly dominates the
    expected utility under any single-deviator variant. -/
theorem spsb3_bidder1_kernel_dominance (n : Nat) (bid : Fin n → Fin n)
    (v_joint : Fin ((n * n) * n)) :
    auctionBidder1Util3 n (detMatrix (spsbAuctionFn3 n)) v_joint
    ≥ auctionBidder1Util3 n
        (detMatrix (spsbAuctionDeviator1Fn3 n bid)) v_joint := by
  rw [auctionBidder1Util3_det, auctionBidder1Util3_det]
  unfold spsbAuctionFn3 spsbAuctionDeviator1Fn3
  rw [Fin.first_pair, Fin.first_pair, Fin.first_pair, Fin.first_pair]
  exact_mod_cast vickrey3_truthful_dominant n
    (Fin.first (Fin.first v_joint))
    (bid (Fin.first (Fin.first v_joint)))
    (Fin.second (Fin.first v_joint))
    (Fin.second v_joint)

end AuctionCat
