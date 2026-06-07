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

/-! ## Three-bidder open-game-pipeline connection

  Mirrors the two-bidder connection in `AuctionCat.KernelTruth`:
  identifies `(auctionGame3 n).view` and `(auctionGame3 n).update`
  as `detMatrix` kernels, then chains via `detMatrix_comp` and
  `kron_detMatrix` to express the full Vickrey3 score kernel as a
  deterministic outcome function. -/

/-- The deterministic underlying function of `(auctionGame3 n).view`:
    given a joint valuation `v : Fin ((n * n) * n)`, duplicate it. -/
def auctionViewFn3 (n : Nat) (v : Fin ((n * n) * n)) :
    Fin (((n * n) * n) * ((n * n) * n)) :=
  Fin.pair v v

/-- The deterministic underlying function of `(auctionGame3 n).update`.
    Routes bidders 1+2 through `auctionUpdateFn`, bidder 3 through
    `truthfulUtilityFn`. -/
def auctionUpdateFn3 (n : Nat)
    (x : Fin (((n * n) * n) * (((2 * n) * (2 * n)) * (2 * n)))) :
    Fin ((n * n) * n) :=
  Fin.pair
    (auctionUpdateFn n
       (Fin.pair (Fin.first (Fin.first x)) (Fin.first (Fin.second x))))
    (truthfulUtilityFn n
       (Fin.pair (Fin.second (Fin.first x)) (Fin.second (Fin.second x))))

/-- `(auctionGame3 n).view = detMatrix (auctionViewFn3 n)`. -/
theorem auctionGame3_view_eq_detMatrix (n : Nat) :
    (auctionGame3 n).view = detMatrix (auctionViewFn3 n) := by
  have h_mid : (OpenGamesCat.middleInterchange (n * n) (n * n) n n :
                  StochasticMatrix (((n * n) * (n * n)) * (n * n))
                                   (((n * n) * n) * ((n * n) * n)))
              = detMatrix (middleInterchangeFn (n * n) (n * n) n n) :=
    middleInterchange_eq_detMatrix (n * n) (n * n) n n
  have h_view : (auctionGame3 n).view
              = StochasticMatrix.comp
                  (StochasticMatrix.kron (detMatrix (auctionViewFn n))
                                          (detMatrix (@copyFin n)))
                  (detMatrix (middleInterchangeFn (n * n) (n * n) n n)) := by
    show StochasticMatrix.comp
          (StochasticMatrix.kron (auctionGame n).view (copy n))
          (OpenGamesCat.middleInterchange (n * n) (n * n) n n :
              StochasticMatrix (((n * n) * (n * n)) * (n * n))
                               (((n * n) * n) * ((n * n) * n)))
        = _
    rw [auctionGame_view_eq_detMatrix, copy_eq_detMatrix, h_mid]
    rfl
  rw [h_view, kron_detMatrix, detMatrix_comp]
  congr 1
  funext v
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have hnn_nn : 0 < (n * n) * (n * n) := Nat.mul_pos hnn hnn
  unfold middleInterchangeFn auctionViewFn copyFin auctionViewFn3
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn,
             Fin.second_pair hnn_nn]
  rw [Fin.pair_first_second v]

/-- `(auctionGame3 n).update = detMatrix (auctionUpdateFn3 n)`. -/
theorem auctionGame3_update_eq_detMatrix (n : Nat) :
    (auctionGame3 n).update = detMatrix (auctionUpdateFn3 n) := by
  have h_mid : (OpenGamesCat.middleInterchange (n * n) n
                    ((2 * n) * (2 * n)) (2 * n) :
                  StochasticMatrix
                    (((n * n) * n) * (((2 * n) * (2 * n)) * (2 * n)))
                    (((n * n) * ((2 * n) * (2 * n))) * (n * (2 * n))))
              = detMatrix
                  (middleInterchangeFn (n * n) n ((2 * n) * (2 * n)) (2 * n)) :=
    middleInterchange_eq_detMatrix (n * n) n ((2 * n) * (2 * n)) (2 * n)
  have h_update : (auctionGame3 n).update
                = StochasticMatrix.comp
                    (detMatrix
                      (middleInterchangeFn (n * n) n ((2 * n) * (2 * n)) (2 * n)))
                    (StochasticMatrix.kron
                      (detMatrix (auctionUpdateFn n))
                      (detMatrix (truthfulUtilityFn n))) := by
    show StochasticMatrix.comp
          (OpenGamesCat.middleInterchange (n * n) n
              ((2 * n) * (2 * n)) (2 * n) :
              StochasticMatrix
                (((n * n) * n) * (((2 * n) * (2 * n)) * (2 * n)))
                (((n * n) * ((2 * n) * (2 * n))) * (n * (2 * n))))
          (StochasticMatrix.kron (auctionGame n).update
                                  (detMatrix (truthfulUtilityFn n)))
        = _
    rw [auctionGame_update_eq_detMatrix, h_mid]
    rfl
  rw [h_update, kron_detMatrix, detMatrix_comp]
  congr 1
  funext x
  have h_inputs : 0 < ((n * n) * n) * (((2 * n) * (2 * n)) * (2 * n)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hLeft : 0 < (n * n) * n := Nat.pos_of_mul_pos_right h_inputs
  have hRight : 0 < ((2 * n) * (2 * n)) * (2 * n) :=
    Nat.pos_of_mul_pos_left h_inputs
  have hn2n2n : 0 < (2 * n) * (2 * n) := Nat.pos_of_mul_pos_right hRight
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hLeft
  have h_nn_2n2n : 0 < (n * n) * ((2 * n) * (2 * n)) :=
    Nat.mul_pos hnn hn2n2n
  unfold middleInterchangeFn auctionUpdateFn3
  simp only [Fin.first_pair, Fin.second_pair h_nn_2n2n]

/-- Bidder 1's 3-bidder truthful utility against the spsb3 outcome
    matches `vickreyUtility3 v1 v1 v2 v3`.  Both fire on the same
    condition `v1 ≥ v2 ∧ v1 ≥ v3`. -/
theorem truthfulUtility_spsb3Fn_bidder1 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.first (Fin.first v_joint))
                  (Fin.first (Fin.first (spsb3Fn n v_joint))))
    = vickreyUtility3 n (Fin.first (Fin.first v_joint))
                        (Fin.first (Fin.first v_joint))
                        (Fin.second (Fin.first v_joint))
                        (Fin.second v_joint) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2n : 0 < 2 * n := by omega
  have h2 : 0 < 2 := by decide
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  -- Use v_joint.val divmod form so it matches simp's normalized goal.
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_first :
        Fin.first (Fin.first (spsb3Fn n v_joint))
        = Fin.pair (⟨1, by decide⟩ : Fin 2)
            (⟨max (v_joint.val % (n * n) / n) (v_joint.val / (n * n)),
              by have hv := v_joint.isLt
                 have h1 : v_joint.val % (n * n) / n < n :=
                   Nat.div_lt_of_lt_mul (Nat.mod_lt _ hnn)
                 have h2 : v_joint.val / (n * n) < n :=
                   Nat.div_lt_of_lt_mul (by omega)
                 omega⟩ : Fin n) := by
      unfold spsb3Fn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyUtility3
    simp [Fin.first_pair, Fin.second_pair hn, hwin1]
    omega
  · have h_first :
        Fin.first (Fin.first (spsb3Fn n v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3Fn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyUtility3
    simp [Fin.first_pair, Fin.second_pair hn, hwin1]

/-- Bidder 2's 3-bidder truthful utility against the spsb3 outcome
    matches `vickreyUtility3 v2 v2 v1 v3`.  The win conditions
    differ but both branches produce 0 when ties cause the win to
    flip to bidder 1. -/
theorem truthfulUtility_spsb3Fn_bidder2 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second (Fin.first v_joint))
                  (Fin.second (Fin.first (spsb3Fn n v_joint))))
    = vickreyUtility3 n (Fin.second (Fin.first v_joint))
                        (Fin.second (Fin.first v_joint))
                        (Fin.first (Fin.first v_joint))
                        (Fin.second v_joint) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2n : 0 < 2 * n := by omega
  have h2 : 0 < 2 := by decide
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  have hv2_lt : v_joint.val % (n * n) / n < n :=
    Nat.div_lt_of_lt_mul (Nat.mod_lt _ hnn)
  have hv3_lt : v_joint.val / (n * n) < n :=
    Nat.div_lt_of_lt_mul (by have := v_joint.isLt; omega)
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_second :
        Fin.second (Fin.first (spsb3Fn n v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3Fn
      simp [hwin1, Fin.first_pair, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyUtility3
    by_cases hcond : v_joint.val % (n * n) / n ≥ v_joint.val % n
                    ∧ v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
    · -- Tie case: v1 = v2 (both directions ≥), so max(v1,v3) = v2.
      have hmax : max (v_joint.val % n) (v_joint.val / (n * n))
                = v_joint.val % (n * n) / n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
    · simp [Fin.first_pair, Fin.second_pair hn, hcond]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
    · -- Bidder 2 wins.
      have h_second :
          Fin.second (Fin.first (spsb3Fn n v_joint))
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (⟨max (v_joint.val % n) (v_joint.val / (n * n)),
                by have := hv3_lt; have := Nat.mod_lt v_joint.val hn; omega⟩
                : Fin n) := by
        unfold spsb3Fn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyUtility3
      have hge : v_joint.val % (n * n) / n ≥ v_joint.val % n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hge, hwin2]
      omega
    · -- Bidder 3 wins; bidder 2 also loses.
      have h_second :
          Fin.second (Fin.first (spsb3Fn n v_joint))
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsb3Fn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyUtility3
      simp [Fin.first_pair, Fin.second_pair hn, hwin2]

/-- Bidder 3's 3-bidder truthful utility against the spsb3 outcome
    matches `vickreyUtility3 v3 v3 v1 v2`. -/
theorem truthfulUtility_spsb3Fn_bidder3 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second v_joint)
                  (Fin.second (spsb3Fn n v_joint)))
    = vickreyUtility3 n (Fin.second v_joint) (Fin.second v_joint)
                        (Fin.first (Fin.first v_joint))
                        (Fin.second (Fin.first v_joint)) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2n : 0 < 2 * n := by omega
  have h2 : 0 < 2 := by decide
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  have hv2_lt : v_joint.val % (n * n) / n < n :=
    Nat.div_lt_of_lt_mul (Nat.mod_lt _ hnn)
  have hv3_lt : v_joint.val / (n * n) < n :=
    Nat.div_lt_of_lt_mul (by have := v_joint.isLt; omega)
  have hv1_lt : v_joint.val % n < n := Nat.mod_lt _ hn
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_second :
        Fin.second (spsb3Fn n v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3Fn
      simp [hwin1, Fin.second_pair h2n2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyUtility3
    by_cases hcond : v_joint.val / (n * n) ≥ v_joint.val % n
                    ∧ v_joint.val / (n * n) ≥ v_joint.val % (n * n) / n
    · have hmax : max (v_joint.val % n) (v_joint.val % (n * n) / n)
                = v_joint.val / (n * n) := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
    · simp [Fin.first_pair, Fin.second_pair hn, hcond]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
    · have h_second :
          Fin.second (spsb3Fn n v_joint)
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsb3Fn
        simp [hwin1, hwin2, Fin.second_pair h2n2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyUtility3
      by_cases hcond : v_joint.val / (n * n) ≥ v_joint.val % n
                      ∧ v_joint.val / (n * n) ≥ v_joint.val % (n * n) / n
      · have hmax : max (v_joint.val % n) (v_joint.val % (n * n) / n)
                  = v_joint.val / (n * n) := by omega
        simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
      · simp [Fin.first_pair, Fin.second_pair hn, hcond]
    · have h_second :
          Fin.second (spsb3Fn n v_joint)
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (⟨max (v_joint.val % n) (v_joint.val % (n * n) / n),
                by have := hv1_lt; have := hv2_lt; omega⟩ : Fin n) := by
        unfold spsb3Fn
        simp [hwin1, hwin2, Fin.second_pair h2n2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyUtility3
      have hge1 : v_joint.val / (n * n) ≥ v_joint.val % n := by omega
      have hge2 : v_joint.val / (n * n)
                ≥ v_joint.val % (n * n) / n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hge1, hge2]
      omega

/-- **Open-game-pipeline connection (3 bidders)**: the three-bidder
    Vickrey `spsb3Auction n` kernel equals the deterministic kernel
    of its closed-form outcome function `spsbAuctionFn3 n`. -/
theorem spsb3Auction_eq_detMatrix (n : Nat) :
    spsb3Auction n = detMatrix (spsbAuctionFn3 n) := by
  have h_score : spsb3Auction n
              = StochasticMatrix.comp ((auctionGame3 n).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix ((n * n) * n))
                                           (secondPriceSealedBid3 n))
                   ((auctionGame3 n).update)) := rfl
  rw [h_score, auctionGame3_view_eq_detMatrix n,
      auctionGame3_update_eq_detMatrix n,
      idMatrix_eq_detMatrix ((n * n) * n)]
  show (detMatrix (auctionViewFn3 n)).comp
        ((StochasticMatrix.kron (detMatrix (fun i : Fin ((n * n) * n) => i))
                                 (detMatrix (spsb3Fn n))).comp
         (detMatrix (auctionUpdateFn3 n)))
      = detMatrix (spsbAuctionFn3 n)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  unfold auctionViewFn3 auctionUpdateFn3 spsbAuctionFn3
  simp only [Fin.first_pair, Fin.second_pair hnnn]
  unfold auctionUpdateFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_spsb3Fn_bidder1,
      truthfulUtility_spsb3Fn_bidder2,
      truthfulUtility_spsb3Fn_bidder3]

/-- **Pipeline-level Vickrey truthfulness** (bidder 1, 3 bidders).
    Bidder 1's expected utility in the OpenGame-pipeline form of
    `spsb3Auction n` weakly dominates any single-deviator variant. -/
theorem spsb3_bidder1_pipeline_dominance (n : Nat) (bid : Fin n → Fin n)
    (v_joint : Fin ((n * n) * n)) :
    auctionBidder1Util3 n (spsb3Auction n) v_joint
    ≥ auctionBidder1Util3 n
        (detMatrix (spsbAuctionDeviator1Fn3 n bid)) v_joint := by
  rw [spsb3Auction_eq_detMatrix]
  exact spsb3_bidder1_kernel_dominance n bid v_joint

end AuctionCat
