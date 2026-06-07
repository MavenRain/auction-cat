import AuctionCat.FirstPrice3
import AuctionCat.Auction
import AuctionCat.Vickrey3

/-!
# AuctionCat.KernelFirstPrice3

Three-bidder pipeline-level closed-form for `fpsb3Auction n`
(truthful play).

Under truthful bidding in a first-price-sealed-bid auction, every
bidder either loses or wins and pays their own bid = their own
valuation, so utility = `v - v = 0`.  The closed-form outcome is the
constant zero-utility triple, regardless of valuations.

Mirrors the 2-bidder file `AuctionCat.KernelFirstPrice`.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The deterministic outcome of `fpsb3Auction n` at any joint
    valuation under truthful bidding: all three bidders get zero
    utility. -/
def fpsbAuctionFn3 (n : Nat) (v_joint : Fin ((n * n) * n)) :
    Fin ((n * n) * n) :=
  let hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  let hnn  : 0 < n * n     := Nat.pos_of_mul_pos_right hnnn
  let hn   : 0 < n         := Nat.pos_of_mul_pos_right hnn
  Fin.pair (Fin.pair (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n))
           (⟨0, hn⟩ : Fin n)

/-- Bidder 1's truthful utility against the fpsb3 outcome is `0`. -/
theorem truthfulUtility_fpsb3Fn_bidder1 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.first (Fin.first v_joint))
                  (Fin.first (Fin.first (fpsb3Fn n v_joint))))
    = (⟨0, Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right
              (Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt))⟩
        : Fin n) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_first :
        Fin.first (Fin.first (fpsb3Fn n v_joint))
        = Fin.pair (⟨1, by decide⟩ : Fin 2) (Fin.first (Fin.first v_joint)) := by
      unfold fpsb3Fn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
    omega
  · have h_first :
        Fin.first (Fin.first (fpsb3Fn n v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold fpsb3Fn
      simp [hwin1, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]

/-- Bidder 2's truthful utility against the fpsb3 outcome is `0`. -/
theorem truthfulUtility_fpsb3Fn_bidder2 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second (Fin.first v_joint))
                  (Fin.second (Fin.first (fpsb3Fn n v_joint))))
    = (⟨0, Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right
              (Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt))⟩
        : Fin n) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_second :
        Fin.second (Fin.first (fpsb3Fn n v_joint))
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold fpsb3Fn
      simp [hwin1, Fin.first_pair, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
    · have h_second :
          Fin.second (Fin.first (fpsb3Fn n v_joint))
          = Fin.pair (⟨1, by decide⟩ : Fin 2)
              (Fin.second (Fin.first v_joint)) := by
        unfold fpsb3Fn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn
      simp [Fin.first_pair, Fin.second_pair hn]
      omega
    · have h_second :
          Fin.second (Fin.first (fpsb3Fn n v_joint))
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold fpsb3Fn
        simp [hwin1, hwin2, Fin.first_pair, Fin.second_pair h2n]
      rw [h_second]
      unfold truthfulUtilityFn
      simp [Fin.first_pair, Fin.second_pair hn]

/-- Bidder 3's truthful utility against the fpsb3 outcome is `0`. -/
theorem truthfulUtility_fpsb3Fn_bidder3 (n : Nat)
    (v_joint : Fin ((n * n) * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second v_joint)
                  (Fin.second (fpsb3Fn n v_joint)))
    = (⟨0, Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right
              (Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt))⟩
        : Fin n) := by
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  have h2n2n : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  by_cases hwin1 : v_joint.val % n ≥ v_joint.val % (n * n) / n
                 ∧ v_joint.val % n ≥ v_joint.val / (n * n)
  · have h_second :
        Fin.second (fpsb3Fn n v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold fpsb3Fn
      simp [hwin1, Fin.second_pair h2n2n]
    rw [h_second]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
  · by_cases hwin2 : v_joint.val % (n * n) / n ≥ v_joint.val / (n * n)
    · have h_second :
          Fin.second (fpsb3Fn n v_joint)
          = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
        unfold fpsb3Fn
        simp [hwin1, hwin2, Fin.second_pair h2n2n]
      rw [h_second]
      unfold truthfulUtilityFn
      simp [Fin.first_pair, Fin.second_pair hn]
    · have h_second :
          Fin.second (fpsb3Fn n v_joint)
          = Fin.pair (⟨1, by decide⟩ : Fin 2) (Fin.second v_joint) := by
        unfold fpsb3Fn
        simp [hwin1, hwin2, Fin.second_pair h2n2n]
      rw [h_second]
      unfold truthfulUtilityFn
      simp [Fin.first_pair, Fin.second_pair hn]
      omega

/-- **Open-game-pipeline connection for fpsb3 truthful**: the
    three-bidder first-price `fpsb3Auction n` kernel equals the
    deterministic kernel of its closed-form outcome function
    `fpsbAuctionFn3 n` (the constant zero-utility triple). -/
theorem fpsb3Auction_eq_detMatrix (n : Nat) :
    fpsb3Auction n = detMatrix (fpsbAuctionFn3 n) := by
  have h_score : fpsb3Auction n
              = StochasticMatrix.comp ((auctionGame3 n).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix ((n * n) * n))
                                           (firstPriceSealedBid3 n))
                   ((auctionGame3 n).update)) := rfl
  rw [h_score, auctionGame3_view_eq_detMatrix n,
      auctionGame3_update_eq_detMatrix n,
      idMatrix_eq_detMatrix ((n * n) * n)]
  show (detMatrix (auctionViewFn3 n)).comp
        ((StochasticMatrix.kron
            (detMatrix (fun i : Fin ((n * n) * n) => i))
            (detMatrix (fpsb3Fn n))).comp
         (detMatrix (auctionUpdateFn3 n)))
      = detMatrix (fpsbAuctionFn3 n)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewFn3 auctionUpdateFn3 fpsbAuctionFn3
  simp only [Fin.first_pair, Fin.second_pair hnnn]
  unfold auctionUpdateFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_fpsb3Fn_bidder1,
      truthfulUtility_fpsb3Fn_bidder2,
      truthfulUtility_fpsb3Fn_bidder3]

end AuctionCat
