import AuctionCat.Reserve
import AuctionCat.SecondPrice
import AuctionCat.Auction
import AuctionCat.KernelTruth

/-!
# AuctionCat.ReserveTruth

Kernel-level truthfulness and open-game-pipeline connection for
the Vickrey auction with reserve price `r` (two bidders).

Provides:

  - `vickreyReserveUtility` : bidder utility under spsb-with-reserve.
  - `vickreyReserve_truthful_dominant` : truthful is dominant.
  - `spsbReserveAuctionFn` : closed-form deterministic outcome.
  - `spsbReserveAuction_eq_detMatrix` : pipeline ↔ closed-form.
  - `spsbReserveAuctionDeviator1Fn` /
    `spsbReserveAuctionDeviator1_eq_detMatrix` : deviator side.
  - `spsbReserve_bidder1_kernel_dominance` / pipeline dominance.

The reserve modifies the spsb truthfulness in the obvious way: a
bidder wins iff own bid is highest AND meets the reserve; the
winner pays `max r (loser's bid)`.  Truthfulness still holds
because, as in standard Vickrey, the payment is independent of the
winner's own bid.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder 1's truncated utility in a Vickrey-with-reserve auction,
    given valuation `v`, own bid `b1`, opposing bid `b2`, and
    reserve `r`.  Wins iff `b1 ≥ b2 ∧ b1 ≥ r`; pays
    `max r b2` on win. -/
def vickreyReserveUtility (n : Nat) (v b1 b2 r : Fin n) : Fin n :=
  if b1.val ≥ b2.val ∧ b1.val ≥ r.val then
    ⟨v.val - max r.val b2.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness for two-bidder Vickrey with
    reserve: truthful bidding (`b1 = v`) yields utility at least as
    high as any deviation, for any opposing bid `b2` and any
    reserve `r`. -/
theorem vickreyReserve_truthful_dominant (n : Nat) (v b1 b2 r : Fin n) :
    (vickreyReserveUtility n v v b2 r).val
    ≥ (vickreyReserveUtility n v b1 b2 r).val := by
  unfold vickreyReserveUtility
  by_cases hv : v.val ≥ b2.val ∧ v.val ≥ r.val <;>
  by_cases hb : b1.val ≥ b2.val ∧ b1.val ≥ r.val <;>
  simp [hv, hb] <;>
  omega

/-- Bidder 1's truthful utility against the spsbReserve outcome
    matches `vickreyReserveUtility v1 v1 v2 r`. -/
theorem truthfulUtility_spsbReserveFn_bidder1 (n : Nat) (r : Fin n)
    (v_joint : Fin (n * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.first v_joint)
                  (Fin.first (spsbReserveFn n r v_joint)))
    = vickreyReserveUtility n (Fin.first v_joint) (Fin.first v_joint)
                              (Fin.second v_joint) r := by
  have hnn : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  by_cases hwin : v_joint.val % n ≥ v_joint.val / n
                ∧ v_joint.val % n ≥ r.val
  · have h_first :
        Fin.first (spsbReserveFn n r v_joint)
        = Fin.pair (⟨1, by decide⟩ : Fin 2)
            (⟨max r.val (Fin.second v_joint).val,
              by have := r.isLt; have := (Fin.second v_joint).isLt; omega⟩
              : Fin n) := by
      unfold spsbReserveFn
      simp [hwin, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility
    simp [Fin.first_pair, Fin.second_pair hn, hwin]
    omega
  · have h_first :
        Fin.first (spsbReserveFn n r v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsbReserveFn
      simp [hwin, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility
    simp [Fin.first_pair, Fin.second_pair hn, hwin]

/-- Bidder 2's truthful utility against the spsbReserve outcome
    matches `vickreyReserveUtility v2 v2 v1 r`. -/
theorem truthfulUtility_spsbReserveFn_bidder2 (n : Nat) (r : Fin n)
    (v_joint : Fin (n * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second v_joint)
                  (Fin.second (spsbReserveFn n r v_joint)))
    = vickreyReserveUtility n (Fin.second v_joint) (Fin.second v_joint)
                              (Fin.first v_joint) r := by
  have hnn : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val / n
                 ∧ v_joint.val % n ≥ r.val
  · -- Bidder 1 wins; bidder 2 loses.
    have h_second :
        Fin.second (spsbReserveFn n r v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsbReserveFn
      simp [hwin1, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyReserveUtility
    by_cases hcond : v_joint.val / n ≥ v_joint.val % n
                    ∧ v_joint.val / n ≥ r.val
    · have hmax : max r.val (v_joint.val % n) = v_joint.val / n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
    · simp [Fin.first_pair, Fin.second_pair hn, hcond]
  · by_cases hwin2 : v_joint.val / n ≥ r.val
    · -- Bidder 2 wins.
      have h_second :
          Fin.second (spsbReserveFn n r v_joint)
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (⟨max r.val (v_joint.val % n),
                by have := r.isLt; have := Nat.mod_lt v_joint.val hn; omega⟩
                : Fin n) := by
        unfold spsbReserveFn
        simp [hwin1, hwin2, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveUtility
      have hge : v_joint.val / n ≥ v_joint.val % n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hge, hwin2]
      omega
    · -- No one meets reserve; both lose.
      have h_second :
          Fin.second (spsbReserveFn n r v_joint)
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsbReserveFn
        simp [hwin1, hwin2, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveUtility
      simp [Fin.first_pair, Fin.second_pair hn, hwin2]

/-- Generalised bidder-1 reserve identity: separates `v_actual` from
    the submitted bid `b1`. -/
theorem truthfulUtility_spsbReserveFn_general_bidder1 (n : Nat)
    (r v_actual b1 b2 : Fin n) :
    truthfulUtilityFn n
        (Fin.pair v_actual
          (Fin.first (spsbReserveFn n r (Fin.pair b1 b2))))
    = vickreyReserveUtility n v_actual b1 b2 r := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v_actual.isLt
  have h2 : 0 < 2 := by decide
  by_cases hwin : b1.val ≥ b2.val ∧ b1.val ≥ r.val
  · have h_first :
        Fin.first (spsbReserveFn n r (Fin.pair b1 b2))
        = Fin.pair (⟨1, by decide⟩ : Fin 2)
            (⟨max r.val b2.val,
              by have := r.isLt; have := b2.isLt; omega⟩ : Fin n) := by
      unfold spsbReserveFn
      simp [hwin, Fin.first_pair, Fin.second_pair hn]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility
    simp [Fin.first_pair, Fin.second_pair hn, hwin]
    omega
  · have h_first :
        Fin.first (spsbReserveFn n r (Fin.pair b1 b2))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsbReserveFn
      simp [hwin, Fin.first_pair, Fin.second_pair hn]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility
    simp [Fin.first_pair, Fin.second_pair hn, hwin]

/-! ## Closed-form deterministic outcome functions -/

/-- Deterministic outcome of `spsbReserveAuction n r` at joint
    valuation `v_joint` (both bidders truthful). -/
def spsbReserveAuctionFn (n : Nat) (r : Fin n) (v_joint : Fin (n * n)) :
    Fin (n * n) :=
  Fin.pair
    (vickreyReserveUtility n (Fin.first v_joint) (Fin.first v_joint)
                            (Fin.second v_joint) r)
    (vickreyReserveUtility n (Fin.second v_joint) (Fin.second v_joint)
                            (Fin.first v_joint) r)

/-- Deterministic outcome of `spsbReserveAuctionDeviator1 n r bid`. -/
def spsbReserveAuctionDeviator1Fn (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin (n * n)) : Fin (n * n) :=
  Fin.pair
    (vickreyReserveUtility n (Fin.first v_joint) (bid (Fin.first v_joint))
                            (Fin.second v_joint) r)
    (vickreyReserveUtility n (Fin.second v_joint) (Fin.second v_joint)
                            (bid (Fin.first v_joint)) r)

/-! ## Open-game-pipeline connections -/

/-- `spsbReserveAuction n r = detMatrix (spsbReserveAuctionFn n r)`. -/
theorem spsbReserveAuction_eq_detMatrix (n : Nat) (r : Fin n) :
    spsbReserveAuction n r = detMatrix (spsbReserveAuctionFn n r) := by
  have h_score : spsbReserveAuction n r
              = StochasticMatrix.comp ((auctionGame n).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix (n * n))
                                           (spsbReserve n r))
                   ((auctionGame n).update)) := rfl
  rw [h_score, auctionGame_view_eq_detMatrix n,
      auctionGame_update_eq_detMatrix n,
      idMatrix_eq_detMatrix (n * n)]
  show (detMatrix (auctionViewFn n)).comp
        ((StochasticMatrix.kron (detMatrix (fun i : Fin (n * n) => i))
                                 (detMatrix (spsbReserveFn n r))).comp
         (detMatrix (auctionUpdateFn n)))
      = detMatrix (spsbReserveAuctionFn n r)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewFn auctionUpdateFn spsbReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_spsbReserveFn_bidder1,
      truthfulUtility_spsbReserveFn_bidder2]

/-- `spsbReserveAuctionDeviator1 n r bid
    = detMatrix (spsbReserveAuctionDeviator1Fn n r bid)`. -/
theorem spsbReserveAuctionDeviator1_eq_detMatrix
    (n : Nat) (r : Fin n) (bid : Fin n → Fin n) :
    spsbReserveAuctionDeviator1 n r bid
    = detMatrix (spsbReserveAuctionDeviator1Fn n r bid) := by
  have h_score : spsbReserveAuctionDeviator1 n r bid
              = StochasticMatrix.comp ((auctionGameDeviator1 n bid).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix (n * n))
                                           (spsbReserve n r))
                   ((auctionGameDeviator1 n bid).update)) := rfl
  rw [h_score, auctionGameDeviator1_view_eq_detMatrix n bid,
      auctionGameDeviator1_update_eq_auctionGame_update n bid,
      auctionGame_update_eq_detMatrix n,
      idMatrix_eq_detMatrix (n * n)]
  show (detMatrix (auctionViewDeviator1Fn n bid)).comp
        ((StochasticMatrix.kron (detMatrix (fun i : Fin (n * n) => i))
                                 (detMatrix (spsbReserveFn n r))).comp
         (detMatrix (auctionUpdateFn n)))
      = detMatrix (spsbReserveAuctionDeviator1Fn n r bid)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewDeviator1Fn auctionUpdateFn spsbReserveAuctionDeviator1Fn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_spsbReserveFn_general_bidder1]
  have h_b2 := truthfulUtility_spsbReserveFn_bidder2 n r
                (Fin.pair (bid (Fin.first v)) (Fin.second v))
  simp only [Fin.first_pair, Fin.second_pair hn] at h_b2
  rw [h_b2]

/-! ## Kernel-level and pipeline-level dominance -/

/-- **Kernel-level Vickrey-with-reserve truthfulness** (bidder 1). -/
theorem spsbReserve_bidder1_kernel_dominance (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin (n * n)) :
    auctionBidder1Util n
        (detMatrix (spsbReserveAuctionFn n r)) v_joint
    ≥ auctionBidder1Util n
        (detMatrix (spsbReserveAuctionDeviator1Fn n r bid)) v_joint := by
  rw [auctionBidder1Util_det, auctionBidder1Util_det]
  unfold spsbReserveAuctionFn spsbReserveAuctionDeviator1Fn
  rw [Fin.first_pair, Fin.first_pair]
  have h_util := vickreyReserve_truthful_dominant n (Fin.first v_joint)
                   (bid (Fin.first v_joint)) (Fin.second v_joint) r
  exact_mod_cast h_util

/-- **Pipeline-vs-pipeline Vickrey-with-reserve truthfulness**. -/
theorem spsbReserve_bidder1_pipeline_dominates_pipeline (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (v_joint : Fin (n * n)) :
    auctionBidder1Util n (spsbReserveAuction n r) v_joint
    ≥ auctionBidder1Util n (spsbReserveAuctionDeviator1 n r bid) v_joint := by
  rw [spsbReserveAuction_eq_detMatrix,
      spsbReserveAuctionDeviator1_eq_detMatrix]
  exact spsbReserve_bidder1_kernel_dominance n r bid v_joint

/-! ## Bidder-2 symmetric pipeline dominance for spsbReserve -/

/-- Bidder 2's truncated utility in a 2-bidder Vickrey-with-reserve
    auction.  Wins iff `opp_bid < my_bid ∧ my_bid ≥ r`; pays
    `max r opp_bid`. -/
def vickreyReserveBidder2Util (n : Nat) (v opp_bid my_bid r : Fin n) : Fin n :=
  if opp_bid.val < my_bid.val ∧ my_bid.val ≥ r.val then
    ⟨v.val - max r.val opp_bid.val, by have := v.isLt; omega⟩
  else
    ⟨0, by have := v.isLt; omega⟩

/-- Dominant-strategy truthfulness from bidder 2's perspective under
    reserve: truthful bidding weakly dominates any deviation. -/
theorem vickreyReserve_bidder2_truthful_dominant (n : Nat)
    (v opp_bid bid_val r : Fin n) :
    (vickreyReserveBidder2Util n v opp_bid v r).val
    ≥ (vickreyReserveBidder2Util n v opp_bid bid_val r).val := by
  unfold vickreyReserveBidder2Util
  by_cases h1 : opp_bid.val < v.val ∧ v.val ≥ r.val <;>
  by_cases h2 : opp_bid.val < bid_val.val ∧ bid_val.val ≥ r.val <;>
  simp [h1, h2] <;>
  omega

/-- Generalised bidder-2 reserve identity: pipeline bidder-2 utility
    against `spsbReserveFn` at joint bid `(b1, b2)` equals
    `vickreyReserveBidder2Util v_actual b1 b2 r`. -/
theorem truthfulUtility_spsbReserveFn_general_bidder2 (n : Nat)
    (r v_actual b1 b2 : Fin n) :
    truthfulUtilityFn n
        (Fin.pair v_actual (Fin.second (spsbReserveFn n r (Fin.pair b1 b2))))
    = vickreyReserveBidder2Util n v_actual b1 b2 r := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v_actual.isLt
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  by_cases hwin1 : b1.val ≥ b2.val ∧ b1.val ≥ r.val
  · have h_second :
        Fin.second (spsbReserveFn n r (Fin.pair b1 b2))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsbReserveFn
      simp [hwin1, Fin.first_pair, Fin.second_pair hn, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyReserveBidder2Util
    have hnotcond : ¬ (b1.val < b2.val ∧ b2.val ≥ r.val) := by omega
    simp [Fin.first_pair, Fin.second_pair hn, hnotcond]
  · by_cases hwin2 : b2.val ≥ r.val
    · have h_second :
          Fin.second (spsbReserveFn n r (Fin.pair b1 b2))
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (⟨max r.val b1.val,
                by have := r.isLt; have := b1.isLt; omega⟩ : Fin n) := by
        unfold spsbReserveFn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair hn,
              Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveBidder2Util
      have hlt : b1.val < b2.val := by omega
      have hcond : b1.val < b2.val ∧ b2.val ≥ r.val := ⟨hlt, hwin2⟩
      simp [Fin.first_pair, Fin.second_pair hn, hcond]
      omega
    · have h_second :
          Fin.second (spsbReserveFn n r (Fin.pair b1 b2))
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsbReserveFn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair hn,
              Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveBidder2Util
      have hnotcond : ¬ (b1.val < b2.val ∧ b2.val ≥ r.val) := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hnotcond]

/-- The deterministic outcome of `spsbReserveAuctionDeviator2 n r bid`:
    bidder 1 truthful, bidder 2 plays `bid`. -/
def spsbReserveAuctionDeviator2Fn (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin (n * n)) : Fin (n * n) :=
  Fin.pair
    (vickreyReserveUtility n (Fin.first v_joint) (Fin.first v_joint)
                            (bid (Fin.second v_joint)) r)
    (vickreyReserveBidder2Util n (Fin.second v_joint) (Fin.first v_joint)
                                (bid (Fin.second v_joint)) r)

/-- `spsbReserveAuctionDeviator2 n r bid
    = detMatrix (spsbReserveAuctionDeviator2Fn n r bid)`. -/
theorem spsbReserveAuctionDeviator2_eq_detMatrix
    (n : Nat) (r : Fin n) (bid : Fin n → Fin n) :
    spsbReserveAuctionDeviator2 n r bid
    = detMatrix (spsbReserveAuctionDeviator2Fn n r bid) := by
  have h_score : spsbReserveAuctionDeviator2 n r bid
              = StochasticMatrix.comp ((auctionGameDeviator2 n bid).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix (n * n))
                                           (spsbReserve n r))
                   ((auctionGameDeviator2 n bid).update)) := rfl
  rw [h_score, auctionGameDeviator2_view_eq_detMatrix n bid,
      auctionGameDeviator2_update_eq_auctionGame_update n bid,
      auctionGame_update_eq_detMatrix n,
      idMatrix_eq_detMatrix (n * n)]
  show (detMatrix (auctionViewDeviator2Fn n bid)).comp
        ((StochasticMatrix.kron (detMatrix (fun i : Fin (n * n) => i))
                                 (detMatrix (spsbReserveFn n r))).comp
         (detMatrix (auctionUpdateFn n)))
      = detMatrix (spsbReserveAuctionDeviator2Fn n r bid)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewDeviator2Fn auctionUpdateFn spsbReserveAuctionDeviator2Fn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_spsbReserveFn_general_bidder1]
  rw [truthfulUtility_spsbReserveFn_general_bidder2]

/-- **Kernel-level bidder-2 Vickrey-with-reserve truthfulness**. -/
theorem spsbReserve_bidder2_kernel_dominance (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin (n * n)) :
    auctionBidder2Util n (detMatrix (spsbReserveAuctionFn n r)) v_joint
    ≥ auctionBidder2Util n
        (detMatrix (spsbReserveAuctionDeviator2Fn n r bid)) v_joint := by
  rw [auctionBidder2Util_det, auctionBidder2Util_det]
  have hnn : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold spsbReserveAuctionFn spsbReserveAuctionDeviator2Fn
  rw [Fin.second_pair hn, Fin.second_pair hn]
  -- truthful side: vickreyReserveUtility n v2 v2 v1 r
  -- deviator side: vickreyReserveBidder2Util n v2 v1 (bid v2) r
  -- Direct case analysis.
  have hpoint :
      (vickreyReserveUtility n (Fin.second v_joint) (Fin.second v_joint)
                              (Fin.first v_joint) r).val
      ≥ (vickreyReserveBidder2Util n (Fin.second v_joint)
                                    (Fin.first v_joint)
                                    (bid (Fin.second v_joint)) r).val := by
    unfold vickreyReserveUtility vickreyReserveBidder2Util
    by_cases h1 : (Fin.second v_joint).val ≥ (Fin.first v_joint).val
                ∧ (Fin.second v_joint).val ≥ r.val
    · by_cases h2 : (Fin.first v_joint).val < (bid (Fin.second v_joint)).val
                  ∧ (bid (Fin.second v_joint)).val ≥ r.val
      · simp only [Fin.first_val, Fin.second_val] at h1 h2
        simp [h1, h2]
      · simp only [Fin.first_val, Fin.second_val] at h1 h2
        simp [h1, h2]
    · by_cases h2 : (Fin.first v_joint).val < (bid (Fin.second v_joint)).val
                  ∧ (bid (Fin.second v_joint)).val ≥ r.val
      · simp only [Fin.first_val, Fin.second_val] at h1 h2
        simp [h1, h2]
        omega
      · simp only [Fin.first_val, Fin.second_val] at h1 h2
        simp [h1, h2]
  exact_mod_cast hpoint

/-- **Pipeline-vs-pipeline bidder-2 Vickrey-with-reserve truthfulness**. -/
theorem spsbReserve_bidder2_pipeline_dominates_pipeline (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (v_joint : Fin (n * n)) :
    auctionBidder2Util n (spsbReserveAuction n r) v_joint
    ≥ auctionBidder2Util n (spsbReserveAuctionDeviator2 n r bid) v_joint := by
  rw [spsbReserveAuction_eq_detMatrix,
      spsbReserveAuctionDeviator2_eq_detMatrix]
  exact spsbReserve_bidder2_kernel_dominance n r bid v_joint

end AuctionCat
