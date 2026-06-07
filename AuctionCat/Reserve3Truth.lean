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

/-! ## Per-bidder reserve utility identities for `spsb3ReserveFn` -/

/-- Bidder 1's truthful utility against the spsb3Reserve outcome
    matches `vickreyReserveUtility3 v1 v1 v2 v3 r`. -/
theorem truthfulUtility_spsb3ReserveFn_bidder1 (n : Nat) (r : Fin n)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.first (Fin.first v_joint))
                  (Fin.first (Fin.first (spsb3ReserveFn n r v_joint))))
    = vickreyReserveUtility3 n (Fin.first (Fin.first v_joint))
                                (Fin.first (Fin.first v_joint))
                                (Fin.second (Fin.first v_joint))
                                (Fin.second v_joint) r := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
                 ∧ v_joint.val % n ≥ r.val
  · have h_first :
        Fin.first (Fin.first (spsb3ReserveFn n r v_joint))
        = Fin.pair (⟨1, by decide⟩ : Fin 2)
            (⟨max r.val
                 (max (Fin.second (Fin.first v_joint)).val
                      (Fin.second v_joint).val),
              by have := r.isLt
                 have := (Fin.second (Fin.first v_joint)).isLt
                 have := (Fin.second v_joint).isLt; omega⟩ : Fin n) := by
      unfold spsb3ReserveFn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility3
    simp [Fin.first_pair, Fin.second_pair hn, hwin1]
    omega
  · have h_first :
        Fin.first (Fin.first (spsb3ReserveFn n r v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3ReserveFn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn vickreyReserveUtility3
    simp [Fin.first_pair, Fin.second_pair hn, hwin1]

/-- Bidder 2's truthful utility against the spsb3Reserve outcome
    matches `vickreyReserveUtility3 v2 v2 v1 v3 r`. -/
theorem truthfulUtility_spsb3ReserveFn_bidder2 (n : Nat) (r : Fin n)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second (Fin.first v_joint))
                  (Fin.second (Fin.first (spsb3ReserveFn n r v_joint))))
    = vickreyReserveUtility3 n (Fin.second (Fin.first v_joint))
                                (Fin.second (Fin.first v_joint))
                                (Fin.first (Fin.first v_joint))
                                (Fin.second v_joint) r := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
                 ∧ v_joint.val % n ≥ r.val
  · have h_second :
        Fin.second (Fin.first (spsb3ReserveFn n r v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3ReserveFn
      simp [hwin1, Fin.first_pair, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyReserveUtility3
    by_cases hcond : v_joint.val % (n * n) / n ≥ v_joint.val % n
                    ∧ v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
                    ∧ v_joint.val % (n * n) / n ≥ r.val
    · -- Tie case: v1 = v2.
      have hmax : max r.val
                    (max (v_joint.val % n) (v_joint.val / (n * n)))
                = v_joint.val % (n * n) / n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
    · simp [Fin.first_pair, Fin.second_pair hn, hcond]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
                   ∧ v_joint.val % (n * n) / n ≥ r.val
    · have h_second :
          Fin.second (Fin.first (spsb3ReserveFn n r v_joint))
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (⟨max r.val (max (v_joint.val % n) (v_joint.val / (n * n))),
                by have := r.isLt
                   have := Nat.mod_lt v_joint.val hn
                   have := Nat.div_lt_of_lt_mul
                     (by have := v_joint.isLt; omega
                       : v_joint.val < (n * n) * n)
                   omega⟩ : Fin n) := by
        unfold spsb3ReserveFn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveUtility3
      have hge1 : v_joint.val % (n * n) / n ≥ v_joint.val % n := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hge1, hwin2]
      omega
    · have h_second :
          Fin.second (Fin.first (spsb3ReserveFn n r v_joint))
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsb3ReserveFn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveUtility3
      simp [Fin.first_pair, Fin.second_pair hn, hwin2]

/-- Bidder 3's truthful utility against the spsb3Reserve outcome
    matches `vickreyReserveUtility3 v3 v3 v1 v2 r`. -/
theorem truthfulUtility_spsb3ReserveFn_bidder3 (n : Nat) (r : Fin n)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second v_joint)
                  (Fin.second (spsb3ReserveFn n r v_joint)))
    = vickreyReserveUtility3 n (Fin.second v_joint) (Fin.second v_joint)
                                (Fin.first (Fin.first v_joint))
                                (Fin.second (Fin.first v_joint)) r := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
                 ∧ v_joint.val % n ≥ r.val
  · have h_second :
        Fin.second (spsb3ReserveFn n r v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold spsb3ReserveFn
      simp [hwin1, Fin.second_pair h2n2n]
    rw [h_second]
    unfold truthfulUtilityFn vickreyReserveUtility3
    by_cases hcond : v_joint.val / (n * n) ≥ v_joint.val % n
                    ∧ v_joint.val / (n * n) ≥ v_joint.val % (n * n) / n
                    ∧ v_joint.val / (n * n) ≥ r.val
    · have hmax : max r.val
                    (max (v_joint.val % n) (v_joint.val % (n * n) / n))
                = v_joint.val / (n * n) := by omega
      simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
    · simp [Fin.first_pair, Fin.second_pair hn, hcond]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
                   ∧ v_joint.val % (n * n) / n ≥ r.val
    · have h_second :
          Fin.second (spsb3ReserveFn n r v_joint)
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold spsb3ReserveFn
        simp [hwin1, hwin2, Fin.second_pair h2n2n]
      rw [h_second]
      unfold truthfulUtilityFn vickreyReserveUtility3
      by_cases hcond : v_joint.val / (n * n) ≥ v_joint.val % n
                      ∧ v_joint.val / (n * n) ≥ v_joint.val % (n * n) / n
                      ∧ v_joint.val / (n * n) ≥ r.val
      · -- Tie: v3 = v2.
        have hmax : max r.val
                      (max (v_joint.val % n) (v_joint.val % (n * n) / n))
                  = v_joint.val / (n * n) := by omega
        simp [Fin.first_pair, Fin.second_pair hn, hcond, hmax]
      · simp [Fin.first_pair, Fin.second_pair hn, hcond]
    · by_cases hwin3 : v_joint.val / (n * n) ≥ r.val
      · have h_second :
            Fin.second (spsb3ReserveFn n r v_joint)
            = Fin.pair (⟨1, by decide⟩ : Fin 2)
                (⟨max r.val
                     (max (v_joint.val % n) (v_joint.val % (n * n) / n)),
                  by have := r.isLt
                     have := Nat.mod_lt v_joint.val hn
                     have : v_joint.val % (n * n) / n < n :=
                       Nat.div_lt_of_lt_mul (Nat.mod_lt _ hnn)
                     omega⟩ : Fin n) := by
          unfold spsb3ReserveFn
          simp [hwin1, hwin2, hwin3, Fin.second_pair h2n2n]
        rw [h_second]
        unfold truthfulUtilityFn vickreyReserveUtility3
        have hge1 : v_joint.val / (n * n) ≥ v_joint.val % n := by omega
        have hge2 : v_joint.val / (n * n)
                  ≥ v_joint.val % (n * n) / n := by omega
        simp [Fin.first_pair, Fin.second_pair hn, hge1, hge2, hwin3]
        omega
      · have h_second :
            Fin.second (spsb3ReserveFn n r v_joint)
            = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
          unfold spsb3ReserveFn
          simp [hwin1, hwin2, hwin3, Fin.second_pair h2n2n]
        rw [h_second]
        unfold truthfulUtilityFn vickreyReserveUtility3
        simp [Fin.first_pair, Fin.second_pair hn, hwin3]

/-! ## Open-game-pipeline connection -/

/-- `spsb3ReserveAuction n r = detMatrix (spsb3ReserveAuctionFn n r)`. -/
theorem spsb3ReserveAuction_eq_detMatrix (n : Nat) (r : Fin n) :
    spsb3ReserveAuction n r = detMatrix (spsb3ReserveAuctionFn n r) := by
  have h_score : spsb3ReserveAuction n r
              = StochasticMatrix.comp ((auctionGame3 n).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix ((n * n) * n))
                                           (spsb3Reserve n r))
                   ((auctionGame3 n).update)) := rfl
  rw [h_score, auctionGame3_view_eq_detMatrix n,
      auctionGame3_update_eq_detMatrix n,
      idMatrix_eq_detMatrix ((n * n) * n)]
  show (detMatrix (auctionViewFn3 n)).comp
        ((StochasticMatrix.kron
            (detMatrix (fun i : Fin ((n * n) * n) => i))
            (detMatrix (spsb3ReserveFn n r))).comp
         (detMatrix (auctionUpdateFn3 n)))
      = detMatrix (spsb3ReserveAuctionFn n r)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewFn3 auctionUpdateFn3 spsb3ReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hnnn]
  unfold auctionUpdateFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_spsb3ReserveFn_bidder1,
      truthfulUtility_spsb3ReserveFn_bidder2,
      truthfulUtility_spsb3ReserveFn_bidder3]

/-- **Pipeline-level three-bidder Vickrey-with-reserve truthfulness**.
    Bidder 1's expected utility in the OpenGame-pipeline form of
    `spsb3ReserveAuction n r` weakly dominates the expected utility
    in any single-deviator deterministic-outcome-function variant. -/
theorem spsb3Reserve_bidder1_pipeline_dominance (n : Nat) (r : Fin n)
    (bid : Fin n → Fin n) (v_joint : Fin ((n * n) * n)) :
    auctionBidder1Util3 n (spsb3ReserveAuction n r) v_joint
    ≥ auctionBidder1Util3 n
        (detMatrix (spsb3ReserveAuctionDeviator1Fn n r bid)) v_joint := by
  rw [spsb3ReserveAuction_eq_detMatrix]
  exact spsb3Reserve_bidder1_kernel_dominance n r bid v_joint

end AuctionCat
