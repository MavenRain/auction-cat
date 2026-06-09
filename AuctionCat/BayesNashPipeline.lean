import AuctionCat.BayesNash
import AuctionCat.KernelTruth
import AuctionCat.ReserveTruth
import AuctionCat.Reserve3Truth
import AuctionCat.Envelope

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

/-! ## Three-bidder reserve-spsb pipeline Bayes-Nash -/

/-- Bidder 1's expected utility in a 3-bidder Vickrey-with-reserve
    auction under strategy profile `(s1, s2, s3)`, reserve `r`, and
    joint prior `p23` on bidders 2's and 3's valuations. -/
def vickreyReserveExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v1 : Fin n)
    (p23 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v23 : Fin (n * n) =>
    p23 v23 *
      ((vickreyReserveUtility3 n v1 (s1 v1) (s2 (Fin.first v23))
                                 (s3 (Fin.second v23)) r).val
              : Nat).cast)

/-- Truthful bidding is a best response under 3-bidder reserve-spsb
    against any opposing strategies, for any joint prior with
    nonnegative weights. -/
theorem vickreyReserve3_truthful_best_response (n : Nat) (r : Fin n)
    (s1' s2 s3 : Fin n → Fin n) (p23 : Fin (n * n) → Rat)
    (h_nn : ∀ v23, 0 ≤ p23 v23) (v1 : Fin n) :
    vickreyReserveExpectedUtility3 n r (fun v => v) s2 s3 v1 p23
    ≥ vickreyReserveExpectedUtility3 n r s1' s2 s3 v1 p23 := by
  unfold vickreyReserveExpectedUtility3
  apply Fin.sumRat_le_local
  intro v23
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v23)
  have := vickreyReserve3_truthful_dominant n v1 (s1' v1)
            (s2 (Fin.first v23)) (s3 (Fin.second v23)) r
  exact_mod_cast this

/-- Under truthful play, the pipeline-level expected utility of
    `spsb3ReserveAuction n r` reduces to the kernel-level
    `vickreyReserveExpectedUtility3` with three truthful strategies. -/
theorem auctionExpectedBidder1Util3_spsb3ReserveAuction_eq (n : Nat)
    (r : Fin n) (prior23 : Fin (n * n) → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3ReserveAuction n r) prior23 v1
    = vickreyReserveExpectedUtility3 n r (fun v => v) (fun v => v)
                                          (fun v => v) v1 prior23 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder1Util3 vickreyReserveExpectedUtility3
  congr 1
  funext v23
  rw [spsb3ReserveAuction_eq_detMatrix, auctionBidder1Util3_det]
  unfold spsb3ReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- Under a single-bidder-1 deviator strategy `bid`, the pipeline-level
    expected utility of `spsb3ReserveAuctionDeviator1 n r bid` reduces
    to the kernel-level `vickreyReserveExpectedUtility3` with
    `(bid, truthful, truthful)`. -/
theorem auctionExpectedBidder1Util3_spsb3ReserveAuctionDeviator1_eq
    (n : Nat) (r : Fin n) (bid : Fin n → Fin n)
    (prior23 : Fin (n * n) → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3ReserveAuctionDeviator1 n r bid)
                                  prior23 v1
    = vickreyReserveExpectedUtility3 n r bid (fun v => v) (fun v => v)
                                          v1 prior23 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v1.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder1Util3 vickreyReserveExpectedUtility3
  congr 1
  funext v23
  rw [spsb3ReserveAuctionDeviator1_eq_detMatrix, auctionBidder1Util3_det]
  unfold spsb3ReserveAuctionDeviator1Fn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- **Three-bidder pipeline-level best response for spsbReserve**.
    Truthful bidding gives bidder 1 the highest expected utility
    against `spsb3ReserveAuction n r` (truthful bidders 2, 3) under
    any joint prior with nonnegative weights, beating any deviator
    strategy. -/
theorem spsb3ReserveAuction_truthful_best_response_pipeline (n : Nat)
    (r : Fin n) (prior23 : Fin (n * n) → Rat)
    (h_nn : ∀ v, 0 ≤ prior23 v) (bid : Fin n → Fin n) (v1 : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3ReserveAuction n r) prior23 v1
    ≥ auctionExpectedBidder1Util3 n (spsb3ReserveAuctionDeviator1 n r bid)
                                     prior23 v1 := by
  rw [auctionExpectedBidder1Util3_spsb3ReserveAuction_eq,
      auctionExpectedBidder1Util3_spsb3ReserveAuctionDeviator1_eq]
  exact vickreyReserve3_truthful_best_response n r bid (fun v => v)
    (fun v => v) prior23 h_nn v1

/-! ## Pipeline ↔ envelope theorem connection

  The envelope theorem `vickrey_envelope` says
  `vickreyEqUtility = vickreyEnvelopeIntegral`.  Combined with the
  pipeline equivalence, this yields:

  bidder 1's expected pipeline utility under truthful `spsbAuction n`
  = Myerson envelope integral of the Vickrey allocation rule.

  This is the foundation of revenue equivalence: two auctions whose
  allocation rules agree yield the same expected pipeline utility
  (and hence the same expected revenue). -/

/-- The pipeline-level expected utility under truthful `spsbAuction n`
    coincides with the kernel-level `vickreyEqUtility`. -/
theorem auctionExpectedBidder1Util_spsbAuction_eq_vickreyEqUtility
    (n : Nat) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbAuction n) prior v1
    = vickreyEqUtility n prior v1 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq]
  rfl

/-- **Pipeline ↔ Myerson envelope**: bidder 1's expected pipeline
    utility under truthful `spsbAuction n` equals the Myerson
    envelope integral `Σ_{t < v1} vickreyAllocation t`. -/
theorem auctionExpectedBidder1Util_spsbAuction_eq_envelopeIntegral
    (n : Nat) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbAuction n) prior v1
    = vickreyEnvelopeIntegral n prior v1 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq_vickreyEqUtility]
  exact vickrey_envelope n prior v1

/-- Bidder 1's equilibrium expected utility at type `v1` under
    Vickrey-with-reserve with both bidders truthful and prior `p` on
    bidder 2's valuation.  Reserve-side analog of `vickreyEqUtility`. -/
def vickreyReserveEqUtility (n : Nat) (r : Fin n)
    (prior : Fin n → Rat) (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    prior v2 * ((vickreyReserveUtility n v1 v1 v2 r).val : Nat).cast)

/-- The pipeline-level expected utility under truthful
    `spsbReserveAuction n r` coincides with `vickreyReserveEqUtility`. -/
theorem auctionExpectedBidder1Util_spsbReserveAuction_eq_vickreyReserveEqUtility
    (n : Nat) (r : Fin n) (prior : Fin n → Rat) (v1 : Fin n) :
    auctionExpectedBidder1Util n (spsbReserveAuction n r) prior v1
    = vickreyReserveEqUtility n r prior v1 := by
  rw [auctionExpectedBidder1Util_spsbReserveAuction_eq]
  rfl

/-! ## Bidder-2 symmetric pipeline Bayes-Nash -/

/-- Bidder 2's expected utility in a 2-bidder Vickrey auction with
    strategies `(s1, s2)`, valuation `v2`, and prior `p` on bidder 1's
    valuation. -/
def vickreyBidder2ExpectedUtility (n : Nat) (s1 s2 : Fin n → Fin n)
    (v2 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v1 : Fin n =>
    p v1 * ((vickreyBidder2Util n v2 (s1 v1) (s2 v2)).val : Nat).cast)

/-- Truthful bidding (`s2 = id`) is bidder 2's best response in
    Vickrey, against any opponent strategy `s1`. -/
theorem vickrey_bidder2_truthful_best_response (n : Nat)
    (s1 s2' : Fin n → Fin n) (p : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ p v) (v2 : Fin n) :
    vickreyBidder2ExpectedUtility n s1 (fun v => v) v2 p
    ≥ vickreyBidder2ExpectedUtility n s1 s2' v2 p := by
  unfold vickreyBidder2ExpectedUtility
  apply Fin.sumRat_le_local
  intro v1
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v1)
  have := vickrey_bidder2_truthful_dominant n v2 (s1 v1) (s2' v2)
  exact_mod_cast this

/-- Bidder 2's expected utility from an auction kernel, averaged over
    bidder 1's valuation under prior `prior`, fixing bidder 2's
    valuation at `v2`. -/
def auctionExpectedBidder2Util (n : Nat)
    (auction : StochasticMatrix (n * n) (n * n))
    (prior : Fin n → Rat) (v2 : Fin n) : Rat :=
  Fin.sumRat (fun v1 : Fin n =>
    prior v1 * auctionBidder2Util n auction (Fin.pair v1 v2))

/-- Bridge: `vickreyUtility n v2 v2 v1 = vickreyBidder2Util n v2 v1 v2`
    pointwise as `Fin n` vals.  Both encode bidder 2's utility under
    truthful Vickrey but with weak vs strict tie-breaking conventions;
    the values agree because the tie-case gives `0` either way. -/
theorem vickreyUtility_val_eq_vickreyBidder2Util_val_truthful
    (n : Nat) (v opp : Fin n) :
    (vickreyUtility n v v opp).val = (vickreyBidder2Util n v opp v).val := by
  unfold vickreyUtility vickreyBidder2Util
  by_cases h : v.val ≥ opp.val <;>
  by_cases h2 : opp.val < v.val <;>
  simp [h, h2] <;>
  omega

/-- Under truthful play, the pipeline-level expected utility of
    `spsbAuction n` for bidder 2 reduces to the kernel-level
    `vickreyBidder2ExpectedUtility` with `(truthful, truthful)`. -/
theorem auctionExpectedBidder2Util_spsbAuction_eq (n : Nat)
    (prior : Fin n → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbAuction n) prior v2
    = vickreyBidder2ExpectedUtility n (fun v => v) (fun v => v) v2 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  unfold auctionExpectedBidder2Util vickreyBidder2ExpectedUtility
  congr 1
  funext v1
  rw [spsbAuction_eq_detMatrix, auctionBidder2Util_det]
  unfold spsbAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn]
  have hbridge :
      (vickreyUtility n v2 v2 v1).val
      = (vickreyBidder2Util n v2 v1 v2).val :=
    vickreyUtility_val_eq_vickreyBidder2Util_val_truthful n v2 v1
  rw [show (((vickreyUtility n v2 v2 v1).val : Nat) : Rat)
        = (((vickreyBidder2Util n v2 v1 v2).val : Nat) : Rat) from by
        exact_mod_cast hbridge]

/-- Under a single-bidder-2 deviator strategy `bid`, the pipeline-level
    expected utility for bidder 2 reduces to the kernel-level
    `vickreyBidder2ExpectedUtility` with `(truthful, bid)`. -/
theorem auctionExpectedBidder2Util_spsbAuctionDeviator2_eq (n : Nat)
    (bid : Fin n → Fin n) (prior : Fin n → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbAuctionDeviator2 n bid) prior v2
    = vickreyBidder2ExpectedUtility n (fun v => v) bid v2 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  unfold auctionExpectedBidder2Util vickreyBidder2ExpectedUtility
  congr 1
  funext v1
  rw [spsbAuctionDeviator2_eq_detMatrix, auctionBidder2Util_det]
  unfold spsbAuctionDeviator2Fn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- **Pipeline-level bidder-2 best response**: truthful bidding gives
    bidder 2 the highest expected utility against `spsbAuction n`
    (truthful bidder 1) under any prior with nonnegative weights,
    beating any deviator strategy `bid`. -/
theorem spsbAuction_bidder2_truthful_best_response_pipeline (n : Nat)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v)
    (bid : Fin n → Fin n) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbAuction n) prior v2
    ≥ auctionExpectedBidder2Util n (spsbAuctionDeviator2 n bid) prior v2 := by
  rw [auctionExpectedBidder2Util_spsbAuction_eq,
      auctionExpectedBidder2Util_spsbAuctionDeviator2_eq]
  exact vickrey_bidder2_truthful_best_response n (fun v => v) bid prior
    h_nn v2

/-- A strategy profile is a *pipeline Bayes-Nash equilibrium of
    spsbAuction* under prior `p` iff neither bidder can improve their
    expected pipeline utility by unilateral deviation.  The
    `IsTruthful*` variant fixes both strategies at truthful. -/
def IsTruthfulPipelineBayesNashSpsbAuction (n : Nat)
    (prior : Fin n → Rat) : Prop :=
  (∀ (bid : Fin n → Fin n) (v1 : Fin n),
    auctionExpectedBidder1Util n (spsbAuction n) prior v1
    ≥ auctionExpectedBidder1Util n (spsbAuctionDeviator1 n bid) prior v1)
  ∧
  (∀ (bid : Fin n → Fin n) (v2 : Fin n),
    auctionExpectedBidder2Util n (spsbAuction n) prior v2
    ≥ auctionExpectedBidder2Util n (spsbAuctionDeviator2 n bid) prior v2)

/-- **Pipeline-level Bayes-Nash truthfulness for spsbAuction**.
    Truthful-truthful is a Bayes-Nash equilibrium at the OpenGame
    pipeline level under any prior with nonnegative weights. -/
theorem spsbAuction_truthful_is_pipeline_bayes_nash (n : Nat)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    IsTruthfulPipelineBayesNashSpsbAuction n prior :=
  ⟨spsbAuction_truthful_best_response_pipeline n prior h_nn,
   spsbAuction_bidder2_truthful_best_response_pipeline n prior h_nn⟩

/-! ## Bidder-2 symmetric pipeline Bayes-Nash for spsbReserve -/

/-- Bidder 2's expected utility in a 2-bidder Vickrey-with-reserve
    auction under strategy profile `(s1, s2)`, reserve `r`, valuation
    `v2`, and prior on bidder 1's valuation. -/
def vickreyReserveBidder2ExpectedUtility (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (v2 : Fin n) (p : Fin n → Rat) : Rat :=
  Fin.sumRat (fun v1 : Fin n =>
    p v1 * ((vickreyReserveBidder2Util n v2 (s1 v1) (s2 v2) r).val
              : Nat).cast)

/-- Truthful bidding (`s2 = id`) is bidder 2's best response in
    reserve-spsb against any opponent strategy `s1`. -/
theorem vickreyReserve_bidder2_truthful_best_response (n : Nat) (r : Fin n)
    (s1 s2' : Fin n → Fin n) (p : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ p v) (v2 : Fin n) :
    vickreyReserveBidder2ExpectedUtility n r s1 (fun v => v) v2 p
    ≥ vickreyReserveBidder2ExpectedUtility n r s1 s2' v2 p := by
  unfold vickreyReserveBidder2ExpectedUtility
  apply Fin.sumRat_le_local
  intro v1
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v1)
  have := vickreyReserve_bidder2_truthful_dominant n v2 (s1 v1) (s2' v2) r
  exact_mod_cast this

/-- Bridge: `vickreyReserveUtility v v opp r = vickreyReserveBidder2Util v opp v r`
    pointwise as `Fin n` vals (both encode bidder 2's utility under
    truthful reserve-spsb with different tie-breaking conventions). -/
theorem vickreyReserveUtility_val_eq_vickreyReserveBidder2Util_val_truthful
    (n : Nat) (v opp r : Fin n) :
    (vickreyReserveUtility n v v opp r).val
    = (vickreyReserveBidder2Util n v opp v r).val := by
  unfold vickreyReserveUtility vickreyReserveBidder2Util
  by_cases hopp : opp.val < v.val
  · by_cases hr : v.val ≥ r.val
    · have hge_opp : v.val ≥ opp.val := by omega
      simp [hge_opp, hr, hopp]
    · have hnotge : ¬ (v.val ≥ opp.val ∧ v.val ≥ r.val) := fun ⟨_, h⟩ => hr h
      have hnotcond : ¬ (opp.val < v.val ∧ v.val ≥ r.val) :=
        fun ⟨_, h⟩ => hr h
      simp [hnotge, hnotcond]
  · by_cases hge : v.val ≥ opp.val
    · have hveq : v.val = opp.val := by omega
      by_cases hr : v.val ≥ r.val
      · have hmax : max r.val opp.val = v.val := by omega
        simp [hge, hr, hopp]
        omega
      · have hnotge : ¬ (v.val ≥ opp.val ∧ v.val ≥ r.val) := fun ⟨_, h⟩ => hr h
        have hnotcond : ¬ (opp.val < v.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h⟩ => hr h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp.val ∧ v.val ≥ r.val) := fun ⟨h, _⟩ => hge h
      have hnotcond : ¬ (opp.val < v.val ∧ v.val ≥ r.val) :=
        fun ⟨h, _⟩ => hopp h
      simp [hnotge, hnotcond]

/-- Under truthful play, the pipeline-level bidder-2 expected utility
    of `spsbReserveAuction n r` reduces to
    `vickreyReserveBidder2ExpectedUtility` with `(truthful, truthful)`. -/
theorem auctionExpectedBidder2Util_spsbReserveAuction_eq (n : Nat)
    (r : Fin n) (prior : Fin n → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbReserveAuction n r) prior v2
    = vickreyReserveBidder2ExpectedUtility n r (fun v => v) (fun v => v)
                                            v2 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  unfold auctionExpectedBidder2Util vickreyReserveBidder2ExpectedUtility
  congr 1
  funext v1
  rw [spsbReserveAuction_eq_detMatrix, auctionBidder2Util_det]
  unfold spsbReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn]
  have hbridge :
      (vickreyReserveUtility n v2 v2 v1 r).val
      = (vickreyReserveBidder2Util n v2 v1 v2 r).val :=
    vickreyReserveUtility_val_eq_vickreyReserveBidder2Util_val_truthful n
      v2 v1 r
  rw [show (((vickreyReserveUtility n v2 v2 v1 r).val : Nat) : Rat)
        = (((vickreyReserveBidder2Util n v2 v1 v2 r).val : Nat) : Rat) from by
        exact_mod_cast hbridge]

/-- Under bidder-2 deviator strategy `bid`, the pipeline-level bidder-2
    expected utility of `spsbReserveAuctionDeviator2 n r bid` reduces
    to `vickreyReserveBidder2ExpectedUtility` with `(truthful, bid)`. -/
theorem auctionExpectedBidder2Util_spsbReserveAuctionDeviator2_eq (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (prior : Fin n → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbReserveAuctionDeviator2 n r bid)
                                  prior v2
    = vickreyReserveBidder2ExpectedUtility n r (fun v => v) bid v2 prior := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  unfold auctionExpectedBidder2Util vickreyReserveBidder2ExpectedUtility
  congr 1
  funext v1
  rw [spsbReserveAuctionDeviator2_eq_detMatrix, auctionBidder2Util_det]
  unfold spsbReserveAuctionDeviator2Fn
  simp only [Fin.first_pair, Fin.second_pair hn]

/-- **Pipeline-level bidder-2 best response for spsbReserve**.
    Truthful bidding gives bidder 2 the highest expected utility
    against `spsbReserveAuction n r` under any prior with nonnegative
    weights, beating any deviator strategy `bid`. -/
theorem spsbReserveAuction_bidder2_truthful_best_response_pipeline
    (n : Nat) (r : Fin n) (prior : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ prior v) (bid : Fin n → Fin n) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbReserveAuction n r) prior v2
    ≥ auctionExpectedBidder2Util n
        (spsbReserveAuctionDeviator2 n r bid) prior v2 := by
  rw [auctionExpectedBidder2Util_spsbReserveAuction_eq,
      auctionExpectedBidder2Util_spsbReserveAuctionDeviator2_eq]
  exact vickreyReserve_bidder2_truthful_best_response n r (fun v => v) bid
    prior h_nn v2

/-- A strategy profile is a *pipeline Bayes-Nash equilibrium of
    spsbReserveAuction* under prior `p`. -/
def IsTruthfulPipelineBayesNashSpsbReserveAuction (n : Nat) (r : Fin n)
    (prior : Fin n → Rat) : Prop :=
  (∀ (bid : Fin n → Fin n) (v1 : Fin n),
    auctionExpectedBidder1Util n (spsbReserveAuction n r) prior v1
    ≥ auctionExpectedBidder1Util n (spsbReserveAuctionDeviator1 n r bid)
                                    prior v1)
  ∧
  (∀ (bid : Fin n → Fin n) (v2 : Fin n),
    auctionExpectedBidder2Util n (spsbReserveAuction n r) prior v2
    ≥ auctionExpectedBidder2Util n (spsbReserveAuctionDeviator2 n r bid)
                                    prior v2)

/-- **Pipeline-level Bayes-Nash truthfulness for spsbReserveAuction**.
    Truthful-truthful is a Bayes-Nash equilibrium at the OpenGame
    pipeline level under any prior with nonnegative weights. -/
theorem spsbReserveAuction_truthful_is_pipeline_bayes_nash (n : Nat)
    (r : Fin n) (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    IsTruthfulPipelineBayesNashSpsbReserveAuction n r prior :=
  ⟨spsbReserveAuction_truthful_best_response_pipeline n r prior h_nn,
   spsbReserveAuction_bidder2_truthful_best_response_pipeline n r prior h_nn⟩

end AuctionCat
