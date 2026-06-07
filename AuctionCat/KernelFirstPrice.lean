import AuctionCat.FirstPrice
import AuctionCat.Auction
import AuctionCat.KernelTruth

/-!
# AuctionCat.KernelFirstPrice

Pipeline-level closed-form for `fpsbAuction n` (truthful play).

Under truthful bidding in a first-price-sealed-bid auction, every
bidder either loses (utility = 0) or wins and pays their own bid =
their own valuation, so utility = `v - v = 0`.  The closed-form
outcome `fpsbAuctionFn n` is the constant zero-utility pair.

This file mirrors the spsb side of `KernelTruth.lean` but for the
degenerate first-price truthful case.  No truthfulness theorem is
proved here (truthful is NOT the equilibrium for fpsb — the
Bayes-Nash equilibrium is half-shading).
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder 1's truthful utility against the fpsb outcome is `0`,
    regardless of who wins (the winner pays own bid = own valuation,
    so utility = `v - v = 0`; the loser gets 0). -/
theorem truthfulUtility_fpsbFn_bidder1 (n : Nat) (v_joint : Fin (n * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.first v_joint) (Fin.first (fpsbFn n v_joint)))
    = (⟨0, Nat.pos_of_mul_pos_right
              (Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt)⟩ : Fin n) := by
  have hnn : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  by_cases hge : v_joint.val % n ≥ v_joint.val / n
  · have h_first :
        Fin.first (fpsbFn n v_joint)
        = Fin.pair (⟨1, by decide⟩ : Fin 2) (Fin.first v_joint) := by
      unfold fpsbFn
      simp [hge, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
    omega
  · have h_first :
        Fin.first (fpsbFn n v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold fpsbFn
      simp [hge, Fin.first_pair]
    rw [h_first]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]

/-- Bidder 2's truthful utility against the fpsb outcome is `0`. -/
theorem truthfulUtility_fpsbFn_bidder2 (n : Nat) (v_joint : Fin (n * n)) :
    truthfulUtilityFn n
        (Fin.pair (Fin.second v_joint) (Fin.second (fpsbFn n v_joint)))
    = (⟨0, Nat.pos_of_mul_pos_right
              (Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt)⟩ : Fin n) := by
  have hnn : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2 : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  by_cases hge : v_joint.val % n ≥ v_joint.val / n
  · have h_second :
        Fin.second (fpsbFn n v_joint)
        = Fin.pair (⟨0, by decide⟩ : Fin 2) (⟨0, hn⟩ : Fin n) := by
      unfold fpsbFn
      simp [hge, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
  · have h_second :
        Fin.second (fpsbFn n v_joint)
        = Fin.pair (⟨1, by decide⟩ : Fin 2) (Fin.second v_joint) := by
      unfold fpsbFn
      simp [hge, Fin.second_pair h2n]
    rw [h_second]
    unfold truthfulUtilityFn
    simp [Fin.first_pair, Fin.second_pair hn]
    omega

/-- **Open-game-pipeline connection for fpsb truthful**: the
    two-bidder first-price `fpsbAuction n` kernel equals the
    deterministic kernel of its closed-form outcome function
    `fpsbAuctionFn n` (the constant zero-utility pair). -/
theorem fpsbAuction_eq_detMatrix (n : Nat) :
    fpsbAuction n = detMatrix (fpsbAuctionFn n) := by
  have h_score : fpsbAuction n
              = StochasticMatrix.comp ((auctionGame n).view)
                 (StochasticMatrix.comp
                   (StochasticMatrix.kron (idMatrix (n * n))
                                           (firstPriceSealedBid n))
                   ((auctionGame n).update)) := rfl
  rw [h_score, auctionGame_view_eq_detMatrix n,
      auctionGame_update_eq_detMatrix n,
      idMatrix_eq_detMatrix (n * n)]
  show (detMatrix (auctionViewFn n)).comp
        ((StochasticMatrix.kron (detMatrix (fun i : Fin (n * n) => i))
                                 (detMatrix (fpsbFn n))).comp
         (detMatrix (auctionUpdateFn n)))
      = detMatrix (fpsbAuctionFn n)
  rw [kron_detMatrix, detMatrix_comp, detMatrix_comp]
  congr 1
  funext v
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hnn
  unfold auctionViewFn auctionUpdateFn fpsbAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  rw [truthfulUtility_fpsbFn_bidder1, truthfulUtility_fpsbFn_bidder2]

end AuctionCat
