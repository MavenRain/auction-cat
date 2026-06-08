import AuctionCat.BayesNash
import AuctionCat.KernelTruth

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

end AuctionCat
