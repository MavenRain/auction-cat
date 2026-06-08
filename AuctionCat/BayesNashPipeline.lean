import AuctionCat.BayesNash
import AuctionCat.KernelTruth
import AuctionCat.ReserveTruth

/-!
# AuctionCat.BayesNashPipeline

Lifts the kernel-level Bayes-Nash theorem
`vickrey_truthful_is_bayes_nash` to the OpenGame-pipeline form of
`spsbAuction n`.

Provides:

  - `auctionExpectedBidder1Util` : bidder 1's expected utility from
    an auction kernel under a prior on bidder 2's valuation.
  - `auctionExpectedBidder1Util_spsbAuction_eq` : equivalence to the
    kernel-level `vickreyExpectedUtility` under truthful bidding.
  - `auctionExpectedBidder1Util_spsbAuctionDeviator1_eq` : same under
    a single-bidder-1 deviator.
  - `spsbAuction_truthful_best_response_pipeline` /
    `spsbAuction_truthful_bayes_nash_pipeline` : the pipeline-level
    Bayes-Nash result.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder 1's expected utility from an auction kernel `auction`,
    averaged over bidder 2's valuation `v2` under prior `prior`,
    fixing bidder 1's valuation at `v1`. -/
def auctionExpectedBidder1Util (n : Nat)
    (auction : StochasticMatrix (n * n) (n * n))
    (prior : Fin n → Rat) (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    prior v2 * auctionBidder1Util n auction (Fin.pair v1 v2))

/-- Under truthful play, the pipeline-level expected utility of
    `spsbAuction n` reduces to the kernel-level
    `vickreyExpectedUtility` with `(truthful, truthful)`. -/
theorem auctionExpectedBidder1Util_spsbAuction_eq (n : Nat)
    (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbAuction n) prior v1
    = vickreyExpectedUtility n (fun v => v) (fun v => v) v1 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util vickreyExpectedUtility
  congr 1
  funext v2
  rw [spsbAuction_eq_detMatrix, auctionBidder1Util_det]
  unfold spsbAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- Under a single-bidder-1 deviator strategy `bid`, the pipeline-level
    expected utility of `spsbAuctionDeviator1 n bid` reduces to the
    kernel-level `vickreyExpectedUtility` with `(bid, truthful)`. -/
theorem auctionExpectedBidder1Util_spsbAuctionDeviator1_eq (n : Nat)
    (bid : Fin n → Fin n) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbAuctionDeviator1 n bid) prior v1
    = vickreyExpectedUtility n bid (fun v => v) v1 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util vickreyExpectedUtility
  congr 1
  funext v2
  rw [spsbAuctionDeviator1_eq_detMatrix, auctionBidder1Util_det]
  unfold spsbAuctionDeviator1Fn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- **Pipeline-level best response**: truthful bidding gives bidder 1
    the highest expected utility against `spsbAuction n` (truthful
    bidder 2) under any prior with nonnegative weights, beating any
    deviator strategy `bid`. -/
theorem spsbAuction_truthful_best_response_pipeline (n : Nat)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v)
    (bid : Fin n → Fin n) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbAuction n) prior v1
    ≥ auctionExpectedBidder1Util n (spsbAuctionDeviator1 n bid) prior v1 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq,
      auctionExpectedBidder1Util_spsbAuctionDeviator1_eq]
  exact vickrey_truthful_best_response n (fun v => v) prior h_nn bid v1

/-! ## Reserve-spsb Bayes-Nash at the pipeline level -/

/-- Bidder 1's expected utility in a 2-bidder Vickrey-with-reserve
    auction under strategy profile `(s1, s2)` and prior `p` on
    bidder 2's valuation. -/
def vickreyReserveExpectedUtility (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (v1 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    p v2 * ((vickreyReserveUtility n v1 (s1 v1) (s2 v2) r).val
              : Nat).cast)

/-- Pointwise inequality on a `Fin`-indexed family lifts to
    inequality on the `Fin.sumRat`.  Local copy of the same lemma
    in `BayesNash.lean` (which is `private` there). -/
private theorem Fin.sumRat_le_local {n : Nat} {f g : Fin n → Rat}
    (h : ∀ i, f i ≤ g i) : Fin.sumRat f ≤ Fin.sumRat g := by
  induction n with
  | zero =>
    rw [Fin.sumRat_zero, Fin.sumRat_zero]
    exact Rat.le_refl
  | succ k ih =>
    rw [Fin.sumRat_succ, Fin.sumRat_succ]
    calc f 0 + Fin.sumRat (fun i => f i.succ)
        ≤ g 0 + Fin.sumRat (fun i => f i.succ) :=
          Rat.add_le_add_right.mpr (h 0)
      _ ≤ g 0 + Fin.sumRat (fun i => g i.succ) :=
          Rat.add_le_add_left.mpr (ih (fun i => h i.succ))

/-- Truthful bidding is a best response under reserve-spsb against
    any opposing strategy, for any prior with nonnegative weights. -/
theorem vickreyReserve_truthful_best_response (n : Nat) (r : Fin n)
    (s1' s2 : Fin n → Fin n) (p : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ p v) (v1 : Fin n) :
    vickreyReserveExpectedUtility n r (fun v => v) s2 v1 p
    ≥ vickreyReserveExpectedUtility n r s1' s2 v1 p := by
  unfold vickreyReserveExpectedUtility
  apply Fin.sumRat_le_local
  intro v2
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v2)
  have := vickreyReserve_truthful_dominant n v1 (s1' v1) (s2 v2) r
  exact_mod_cast this

/-- Under truthful play, the pipeline-level expected utility of
    `spsbReserveAuction n r` reduces to the kernel-level
    `vickreyReserveExpectedUtility` with `(truthful, truthful)`. -/
theorem auctionExpectedBidder1Util_spsbReserveAuction_eq (n : Nat)
    (r : Fin n) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbReserveAuction n r) prior v1
    = vickreyReserveExpectedUtility n r (fun v => v) (fun v => v) v1 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util vickreyReserveExpectedUtility
  congr 1
  funext v2
  rw [spsbReserveAuction_eq_detMatrix, auctionBidder1Util_det]
  unfold spsbReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- Under a single-bidder-1 deviator strategy `bid`, the pipeline-level
    expected utility of `spsbReserveAuctionDeviator1 n r bid` reduces
    to the kernel-level `vickreyReserveExpectedUtility` with
    `(bid, truthful)`. -/
theorem auctionExpectedBidder1Util_spsbReserveAuctionDeviator1_eq (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbReserveAuctionDeviator1 n r bid) prior v1
    = vickreyReserveExpectedUtility n r bid (fun v => v) v1 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util vickreyReserveExpectedUtility
  congr 1
  funext v2
  rw [spsbReserveAuctionDeviator1_eq_detMatrix, auctionBidder1Util_det]
  unfold spsbReserveAuctionDeviator1Fn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- **Pipeline-level best response for spsbReserve**: truthful bidding
    gives bidder 1 the highest expected utility against
    `spsbReserveAuction n r` under any prior with nonnegative
    weights, beating any deviator strategy `bid`. -/
theorem spsbReserveAuction_truthful_best_response_pipeline (n : Nat)
    (r : Fin n) (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v)
    (bid : Fin n → Fin n) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbReserveAuction n r) prior v1
    ≥ auctionExpectedBidder1Util n (spsbReserveAuctionDeviator1 n r bid)
                                    prior v1 := by
  rw [auctionExpectedBidder1Util_spsbReserveAuction_eq,
      auctionExpectedBidder1Util_spsbReserveAuctionDeviator1_eq]
  exact vickreyReserve_truthful_best_response n r bid (fun v => v) prior
    h_nn v1

/-! ## Three-bidder pipeline Bayes-Nash -/

/-- Bidder 1's expected utility from a 3-bidder auction kernel
    `auction`, averaged over the joint valuation `(v2, v3)` of the
    other two bidders under prior `prior23`, fixing bidder 1's
    valuation at `v1`. -/
def auctionExpectedBidder1Util3 (n : Nat)
    (auction : StochasticMatrix ((n * n) * n) ((n * n) * n))
    (prior23 : Fin (n * n) → Rat) (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v23 : Fin (n * n) =>
    prior23 v23 * auctionBidder1Util3 n auction
      (Fin.pair (Fin.pair v1 (Fin.first v23)) (Fin.second v23)))

/-- Under truthful play, the pipeline-level expected utility of
    `spsb3Auction n` reduces to the kernel-level
    `vickreyExpectedUtility3` with three truthful strategies. -/
theorem auctionExpectedBidder1Util3_spsb3Auction_eq (n : Nat)
    (prior23 : Fin (n * n) → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3Auction n) prior23 v1
    = vickreyExpectedUtility3 n (fun v => v) (fun v => v) (fun v => v)
                                v1 prior23 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util3 vickreyExpectedUtility3
  congr 1
  funext v23
  rw [spsb3Auction_eq_detMatrix, auctionBidder1Util3_det]
  unfold spsbAuctionFn3
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- Under a single-bidder-1 deviator strategy `bid`, the pipeline-level
    expected utility of `spsb3AuctionDeviator1 n bid` reduces to the
    kernel-level `vickreyExpectedUtility3` with `(bid, truthful, truthful)`. -/
theorem auctionExpectedBidder1Util3_spsb3AuctionDeviator1_eq (n : Nat)
    (bid : Fin n → Fin n) (prior23 : Fin (n * n) → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3AuctionDeviator1 n bid) prior23 v1
    = vickreyExpectedUtility3 n bid (fun v => v) (fun v => v) v1 prior23 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  unfold auctionExpectedBidder1Util3 vickreyExpectedUtility3
  congr 1
  funext v23
  rw [spsb3AuctionDeviator1_eq_detMatrix, auctionBidder1Util3_det]
  unfold spsbAuctionDeviator1Fn3
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- **Three-bidder pipeline-level best response**: truthful bidding
    gives bidder 1 the highest expected utility against
    `spsb3Auction n` (truthful bidders 2, 3) under any joint prior
    with nonnegative weights, beating any deviator strategy. -/
theorem spsb3Auction_truthful_best_response_pipeline (n : Nat)
    (prior23 : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior23 v)
    (bid : Fin n → Fin n) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3Auction n) prior23 v1
    ≥ auctionExpectedBidder1Util3 n (spsb3AuctionDeviator1 n bid)
                                     prior23 v1 := by
  rw [auctionExpectedBidder1Util3_spsb3Auction_eq,
      auctionExpectedBidder1Util3_spsb3AuctionDeviator1_eq]
  exact vickrey3_truthful_best_response n bid (fun v => v) (fun v => v)
    prior23 h_nn v1

end AuctionCat
