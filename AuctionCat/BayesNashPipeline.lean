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

/-- **Pipeline ↔ Myerson envelope (bidder 2)**: by Vickrey symmetry,
    bidder 2's expected pipeline utility under truthful `spsbAuction n`
    also equals the Myerson envelope integral, evaluated at bidder 2's
    valuation.

    Both bidders have the same expected-utility profile because
    spsbAuction is symmetric under bidder swap. -/
theorem auctionExpectedBidder2Util_spsbAuction_eq_envelopeIntegral
    (n : Nat) (prior : Fin n → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util n (spsbAuction n) prior v2
    = vickreyEnvelopeIntegral n prior v2 := by
  rw [auctionExpectedBidder2Util_spsbAuction_eq]
  have hsum :
      vickreyBidder2ExpectedUtility n (fun v => v) (fun v => v) v2 prior
      = vickreyEqUtility n prior v2 := by
    unfold vickreyBidder2ExpectedUtility vickreyEqUtility
    congr 1
    funext v1
    rw [show (((vickreyBidder2Util n v2 v1 v2).val : Nat) : Rat)
          = (((vickreyUtility n v2 v2 v1).val : Nat) : Rat) from by
        exact_mod_cast
          (vickreyUtility_val_eq_vickreyBidder2Util_val_truthful n v2 v1).symm]
  rw [hsum]
  exact vickrey_envelope n prior v2

/-- **Pipeline-level Vickrey symmetry**: under truthful `spsbAuction n`,
    bidder 1 and bidder 2 have equal expected pipeline utility at every
    common valuation, for any prior.  Direct consequence of both
    expected utilities equalling the Myerson envelope integral. -/
theorem spsbAuction_pipeline_utility_symmetric (n : Nat) (prior : Fin n → Rat)
    (v : Fin n) :
    auctionExpectedBidder1Util n (spsbAuction n) prior v
    = auctionExpectedBidder2Util n (spsbAuction n) prior v := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq_envelopeIntegral,
      auctionExpectedBidder2Util_spsbAuction_eq_envelopeIntegral]


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

/-- **Kernel ↔ pipeline consistency**: the truthful-truthful profile
    is a kernel-level Bayes-Nash equilibrium of 2-bidder Vickrey iff
    it is a pipeline-level Bayes-Nash equilibrium of `spsbAuction n`,
    under any prior with nonnegative weights.

    Both directions reduce to the same per-bidder best-response
    inequalities (truthful-dominance), expressed at different
    layers of the framework. -/
theorem IsBayesNashVickrey_iff_pipeline_truthful (n : Nat)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    IsBayesNashVickrey n (fun v => v) (fun v => v) prior
    ↔ IsTruthfulPipelineBayesNashSpsbAuction n prior := by
  refine ⟨fun _ => spsbAuction_truthful_is_pipeline_bayes_nash n prior h_nn,
          fun _ => vickrey_truthful_is_bayes_nash n prior h_nn⟩

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

/-- Kernel-level best response under reserve-spsb (bidder 1's POV). -/
def IsBestResponseVickreyReserve (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    vickreyReserveExpectedUtility n r s1 s2 v1 p
    ≥ vickreyReserveExpectedUtility n r s1' s2 v1 p

/-- Kernel-level Bayes-Nash equilibrium predicate under reserve-spsb. -/
def IsBayesNashVickreyReserve (n : Nat) (r : Fin n)
    (s1 s2 : Fin n → Fin n) (p : Fin n → Rat) : Prop :=
  IsBestResponseVickreyReserve n r s1 s2 p
  ∧ IsBestResponseVickreyReserve n r s2 s1 p

/-- Truthful-truthful is a kernel-level Bayes-Nash equilibrium of
    reserve-spsb, for any prior with nonneg weights. -/
theorem vickreyReserve_truthful_is_bayes_nash (n : Nat) (r : Fin n)
    (p : Fin n → Rat) (h_nn : ∀ v, 0 ≤ p v) :
    IsBayesNashVickreyReserve n r (fun v => v) (fun v => v) p :=
  ⟨fun s1' v1 => vickreyReserve_truthful_best_response n r s1' (fun v => v)
                  p h_nn v1,
   fun s2' v2 => vickreyReserve_truthful_best_response n r s2' (fun v => v)
                  p h_nn v2⟩

/-- **Kernel ↔ pipeline consistency (2-bidder reserve)**. -/
theorem IsBayesNashVickreyReserve_iff_pipeline_truthful (n : Nat) (r : Fin n)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    IsBayesNashVickreyReserve n r (fun v => v) (fun v => v) prior
    ↔ IsTruthfulPipelineBayesNashSpsbReserveAuction n r prior := by
  refine ⟨fun _ => spsbReserveAuction_truthful_is_pipeline_bayes_nash n r
                     prior h_nn,
          fun _ => vickreyReserve_truthful_is_bayes_nash n r prior h_nn⟩

/-! ## 3-bidder pipeline Bayes-Nash (all three bidders) -/

/-- Bidder 2's expected utility in a 3-bidder Vickrey auction with
    strategies `(s1, s2, s3)` and joint prior on (v1, v3) (the other
    two bidders' valuations).  Fix bidder 2's valuation at `v2`. -/
def vickreyBidder2ExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v2 : Fin n) (p13 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v13 : Fin (n * n) =>
    p13 v13 *
      ((vickreyBidder2Util3 n v2 (s1 (Fin.first v13)) (s2 v2)
                                  (s3 (Fin.second v13))).val
              : Nat).cast)

/-- Bidder 3's expected utility in a 3-bidder Vickrey auction with
    strategies `(s1, s2, s3)` and joint prior on (v1, v2). -/
def vickreyBidder3ExpectedUtility3 (n : Nat) (s1 s2 s3 : Fin n → Fin n)
    (v3 : Fin n) (p12 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v12 : Fin (n * n) =>
    p12 v12 *
      ((vickreyBidder3Util3 n v3 (s1 (Fin.first v12)) (s2 (Fin.second v12))
                                  (s3 v3)).val
              : Nat).cast)

/-- Truthful bidding (`s2 = id`) is bidder 2's best response in 3-bidder
    Vickrey, against any opponent strategies. -/
theorem vickrey3_bidder2_truthful_best_response (n : Nat)
    (s1 s2' s3 : Fin n → Fin n) (p13 : Fin (n * n) → Rat)
    (h_nn : ∀ v13, 0 ≤ p13 v13) (v2 : Fin n) :
    vickreyBidder2ExpectedUtility3 n s1 (fun v => v) s3 v2 p13
    ≥ vickreyBidder2ExpectedUtility3 n s1 s2' s3 v2 p13 := by
  unfold vickreyBidder2ExpectedUtility3
  apply Fin.sumRat_le_local
  intro v13
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v13)
  have := vickrey3_bidder2_truthful_dominant n v2
            (s1 (Fin.first v13)) (s2' v2) (s3 (Fin.second v13))
  exact_mod_cast this

/-- Truthful bidding (`s3 = id`) is bidder 3's best response in 3-bidder
    Vickrey, against any opponent strategies. -/
theorem vickrey3_bidder3_truthful_best_response (n : Nat)
    (s1 s2 s3' : Fin n → Fin n) (p12 : Fin (n * n) → Rat)
    (h_nn : ∀ v12, 0 ≤ p12 v12) (v3 : Fin n) :
    vickreyBidder3ExpectedUtility3 n s1 s2 (fun v => v) v3 p12
    ≥ vickreyBidder3ExpectedUtility3 n s1 s2 s3' v3 p12 := by
  unfold vickreyBidder3ExpectedUtility3
  apply Fin.sumRat_le_local
  intro v12
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v12)
  have := vickrey3_bidder3_truthful_dominant n v3
            (s1 (Fin.first v12)) (s2 (Fin.second v12)) (s3' v3)
  exact_mod_cast this

/-- Bidder 2's expected utility from a 3-bidder auction kernel,
    averaged over (v1, v3) under prior `prior13`, fixing v2. -/
def auctionExpectedBidder2Util3 (n : Nat)
    (auction : StochasticMatrix ((n * n) * n) ((n * n) * n))
    (prior13 : Fin (n * n) → Rat) (v2 : Fin n) : Rat :=
  Fin.sumRat (fun v13 : Fin (n * n) =>
    prior13 v13 * auctionBidder2Util3 n auction
      (Fin.pair (Fin.pair (Fin.first v13) v2) (Fin.second v13)))

/-- Bidder 3's expected utility from a 3-bidder auction kernel,
    averaged over (v1, v2) under prior `prior12`, fixing v3. -/
def auctionExpectedBidder3Util3 (n : Nat)
    (auction : StochasticMatrix ((n * n) * n) ((n * n) * n))
    (prior12 : Fin (n * n) → Rat) (v3 : Fin n) : Rat :=
  Fin.sumRat (fun v12 : Fin (n * n) =>
    prior12 v12 * auctionBidder3Util3 n auction
      (Fin.pair v12 v3))

/-- Bridge between vickreyUtility3 and vickreyBidder2Util3 under truthful. -/
theorem vickreyUtility3_val_eq_vickreyBidder2Util3_val_truthful
    (n : Nat) (v opp_b1 opp_b3 : Fin n) :
    (vickreyUtility3 n v v opp_b1 opp_b3).val
    = (vickreyBidder2Util3 n v opp_b1 v opp_b3).val := by
  unfold vickreyUtility3 vickreyBidder2Util3
  by_cases hopp : opp_b1.val < v.val
  · by_cases hb3 : v.val ≥ opp_b3.val
    · have hge_opp : v.val ≥ opp_b1.val := by omega
      simp [hge_opp, hb3, hopp]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val) :=
        fun ⟨_, h⟩ => hb3 h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val) :=
        fun ⟨_, h⟩ => hb3 h
      simp [hnotge, hnotcond]
  · by_cases hge : v.val ≥ opp_b1.val
    · have hveq : v.val = opp_b1.val := by omega
      by_cases hb3 : v.val ≥ opp_b3.val
      · simp [hge, hb3, hopp]
        omega
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val) :=
          fun ⟨_, h⟩ => hb3 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val) :=
          fun ⟨_, h⟩ => hb3 h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val) :=
        fun ⟨h, _⟩ => hge h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val) :=
        fun ⟨h, _⟩ => hopp h
      simp [hnotge, hnotcond]

/-- Bridge between vickreyUtility3 and vickreyBidder3Util3 under truthful. -/
theorem vickreyUtility3_val_eq_vickreyBidder3Util3_val_truthful
    (n : Nat) (v opp_b1 opp_b2 : Fin n) :
    (vickreyUtility3 n v v opp_b1 opp_b2).val
    = (vickreyBidder3Util3 n v opp_b1 opp_b2 v).val := by
  unfold vickreyUtility3 vickreyBidder3Util3
  by_cases hopp1 : opp_b1.val < v.val
  · by_cases hopp2 : opp_b2.val < v.val
    · have hge1 : v.val ≥ opp_b1.val := by omega
      have hge2 : v.val ≥ opp_b2.val := by omega
      simp [hge1, hge2, hopp1, hopp2]
    · -- opp_b2 ≥ v.  If v ≥ opp_b2 also, then opp_b2 = v.  Else ¬h_vickrey.
      by_cases hge2 : v.val ≥ opp_b2.val
      · have hveq : v.val = opp_b2.val := by omega
        have hge1 : v.val ≥ opp_b1.val := by omega
        simp [hge1, hge2, hopp1, hopp2]
        omega
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val) :=
          fun ⟨_, h⟩ => hge2 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val) :=
          fun ⟨_, h⟩ => hopp2 h
        simp [hnotge, hnotcond]
  · by_cases hge1 : v.val ≥ opp_b1.val
    · -- opp_b1 = v
      have hveq1 : v.val = opp_b1.val := by omega
      by_cases hge2 : v.val ≥ opp_b2.val
      · -- vickrey condition holds: v - max(opp_b1, opp_b2) = v - max(v, opp_b2).
        simp [hge1, hge2, hopp1]
        omega
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val) :=
          fun ⟨_, h⟩ => hge2 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val) :=
          fun ⟨h, _⟩ => hopp1 h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val) :=
        fun ⟨h, _⟩ => hge1 h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val) :=
        fun ⟨h, _⟩ => hopp1 h
      simp [hnotge, hnotcond]

/-- Under truthful play, the pipeline-level expected utility for
    bidder 2 reduces to the kernel-level
    `vickreyBidder2ExpectedUtility3` with three truthful strategies. -/
theorem auctionExpectedBidder2Util3_spsb3Auction_eq (n : Nat)
    (prior13 : Fin (n * n) → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3Auction n) prior13 v2
    = vickreyBidder2ExpectedUtility3 n (fun v => v) (fun v => v)
                                       (fun v => v) v2 prior13 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder2Util3 vickreyBidder2ExpectedUtility3
  congr 1
  funext v13
  rw [spsb3Auction_eq_detMatrix, auctionBidder2Util3_det]
  unfold spsbAuctionFn3
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]
  have hbridge :
      (vickreyUtility3 n v2 v2 (Fin.first v13) (Fin.second v13)).val
      = (vickreyBidder2Util3 n v2 (Fin.first v13) v2 (Fin.second v13)).val :=
    vickreyUtility3_val_eq_vickreyBidder2Util3_val_truthful n v2
      (Fin.first v13) (Fin.second v13)
  rw [show (((vickreyUtility3 n v2 v2 (Fin.first v13)
                                       (Fin.second v13)).val : Nat) : Rat)
        = (((vickreyBidder2Util3 n v2 (Fin.first v13) v2
                                       (Fin.second v13)).val : Nat) : Rat)
        from by exact_mod_cast hbridge]

/-- Under bidder-2 deviator strategy `bid`, the pipeline-level expected
    utility for bidder 2 reduces to
    `vickreyBidder2ExpectedUtility3` with `(truthful, bid, truthful)`. -/
theorem auctionExpectedBidder2Util3_spsb3AuctionDeviator2_eq (n : Nat)
    (bid : Fin n → Fin n) (prior13 : Fin (n * n) → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3AuctionDeviator2 n bid) prior13 v2
    = vickreyBidder2ExpectedUtility3 n (fun v => v) bid (fun v => v) v2
                                       prior13 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder2Util3 vickreyBidder2ExpectedUtility3
  congr 1
  funext v13
  rw [spsb3AuctionDeviator2_eq_detMatrix, auctionBidder2Util3_det]
  unfold spsb3AuctionDeviator2Fn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- **Pipeline-level bidder-2 best response in 3-bidder spsb**. -/
theorem spsb3Auction_bidder2_truthful_best_response_pipeline (n : Nat)
    (prior13 : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior13 v)
    (bid : Fin n → Fin n) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3Auction n) prior13 v2
    ≥ auctionExpectedBidder2Util3 n (spsb3AuctionDeviator2 n bid)
                                     prior13 v2 := by
  rw [auctionExpectedBidder2Util3_spsb3Auction_eq,
      auctionExpectedBidder2Util3_spsb3AuctionDeviator2_eq]
  exact vickrey3_bidder2_truthful_best_response n (fun v => v) bid
    (fun v => v) prior13 h_nn v2

/-- Under truthful play, the pipeline-level expected utility for
    bidder 3 reduces to the kernel-level
    `vickreyBidder3ExpectedUtility3` with three truthful strategies. -/
theorem auctionExpectedBidder3Util3_spsb3Auction_eq (n : Nat)
    (prior12 : Fin (n * n) → Rat) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3Auction n) prior12 v3
    = vickreyBidder3ExpectedUtility3 n (fun v => v) (fun v => v)
                                       (fun v => v) v3 prior12 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v3.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder3Util3 vickreyBidder3ExpectedUtility3
  congr 1
  funext v12
  rw [spsb3Auction_eq_detMatrix, auctionBidder3Util3_det]
  unfold spsbAuctionFn3
  simp only [Fin.first_pair, Fin.second_pair hnn]
  have hbridge :
      (vickreyUtility3 n v3 v3 (Fin.first v12) (Fin.second v12)).val
      = (vickreyBidder3Util3 n v3 (Fin.first v12) (Fin.second v12) v3).val :=
    vickreyUtility3_val_eq_vickreyBidder3Util3_val_truthful n v3
      (Fin.first v12) (Fin.second v12)
  rw [show (((vickreyUtility3 n v3 v3 (Fin.first v12)
                                       (Fin.second v12)).val : Nat) : Rat)
        = (((vickreyBidder3Util3 n v3 (Fin.first v12)
                                       (Fin.second v12) v3).val : Nat) : Rat)
        from by exact_mod_cast hbridge]

/-- Under bidder-3 deviator strategy `bid`, the pipeline-level expected
    utility for bidder 3 reduces to
    `vickreyBidder3ExpectedUtility3` with `(truthful, truthful, bid)`. -/
theorem auctionExpectedBidder3Util3_spsb3AuctionDeviator3_eq (n : Nat)
    (bid : Fin n → Fin n) (prior12 : Fin (n * n) → Rat) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3AuctionDeviator3 n bid) prior12 v3
    = vickreyBidder3ExpectedUtility3 n (fun v => v) (fun v => v) bid v3
                                       prior12 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v3.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder3Util3 vickreyBidder3ExpectedUtility3
  congr 1
  funext v12
  rw [spsb3AuctionDeviator3_eq_detMatrix, auctionBidder3Util3_det]
  unfold spsb3AuctionDeviator3Fn
  simp only [Fin.first_pair, Fin.second_pair hnn]

/-- **Pipeline-level bidder-3 best response in 3-bidder spsb**. -/
theorem spsb3Auction_bidder3_truthful_best_response_pipeline (n : Nat)
    (prior12 : Fin (n * n) → Rat) (h_nn : ∀ v, 0 ≤ prior12 v)
    (bid : Fin n → Fin n) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3Auction n) prior12 v3
    ≥ auctionExpectedBidder3Util3 n (spsb3AuctionDeviator3 n bid)
                                     prior12 v3 := by
  rw [auctionExpectedBidder3Util3_spsb3Auction_eq,
      auctionExpectedBidder3Util3_spsb3AuctionDeviator3_eq]
  exact vickrey3_bidder3_truthful_best_response n (fun v => v) (fun v => v)
    bid prior12 h_nn v3

/-- A strategy profile is a *pipeline Bayes-Nash equilibrium of
    spsb3Auction* under priors iff none of the three bidders can
    improve their expected utility by unilateral deviation. -/
def IsTruthfulPipelineBayesNashSpsb3Auction (n : Nat)
    (prior23 : Fin (n * n) → Rat) (prior13 : Fin (n * n) → Rat)
    (prior12 : Fin (n * n) → Rat) : Prop :=
  (∀ (bid : Fin n → Fin n) (v1 : Fin n),
    auctionExpectedBidder1Util3 n (spsb3Auction n) prior23 v1
    ≥ auctionExpectedBidder1Util3 n (spsb3AuctionDeviator1 n bid) prior23 v1)
  ∧
  (∀ (bid : Fin n → Fin n) (v2 : Fin n),
    auctionExpectedBidder2Util3 n (spsb3Auction n) prior13 v2
    ≥ auctionExpectedBidder2Util3 n (spsb3AuctionDeviator2 n bid) prior13 v2)
  ∧
  (∀ (bid : Fin n → Fin n) (v3 : Fin n),
    auctionExpectedBidder3Util3 n (spsb3Auction n) prior12 v3
    ≥ auctionExpectedBidder3Util3 n (spsb3AuctionDeviator3 n bid) prior12 v3)

/-- **Pipeline-level Bayes-Nash truthfulness for 3-bidder spsb**.
    Truthful-truthful-truthful is a Bayes-Nash equilibrium of
    `spsb3Auction n` at the OpenGame pipeline level under any priors
    with nonnegative weights. -/
theorem spsb3Auction_truthful_is_pipeline_bayes_nash (n : Nat)
    (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    IsTruthfulPipelineBayesNashSpsb3Auction n prior23 prior13 prior12 :=
  ⟨spsb3Auction_truthful_best_response_pipeline n prior23 h_nn23,
   spsb3Auction_bidder2_truthful_best_response_pipeline n prior13 h_nn13,
   spsb3Auction_bidder3_truthful_best_response_pipeline n prior12 h_nn12⟩

/-- Bridge: 3-bidder bidder-2 expected utility under truthful equals
    the analogous bidder-1 expected utility. -/
theorem vickreyBidder2ExpectedUtility3_eq_vickreyExpectedUtility3_truthful
    (n : Nat) (v : Fin n) (prior : Fin (n * n) → Rat) :
    vickreyBidder2ExpectedUtility3 n (fun v => v) (fun v => v) (fun v => v)
                                     v prior
    = vickreyExpectedUtility3 n (fun v => v) (fun v => v) (fun v => v)
                                v prior := by
  unfold vickreyBidder2ExpectedUtility3 vickreyExpectedUtility3
  congr 1
  funext v13
  rw [show (((vickreyBidder2Util3 n v (Fin.first v13) v
                                       (Fin.second v13)).val : Nat) : Rat)
        = (((vickreyUtility3 n v v (Fin.first v13)
                                    (Fin.second v13)).val : Nat) : Rat)
        from by
        exact_mod_cast
          (vickreyUtility3_val_eq_vickreyBidder2Util3_val_truthful n v
            (Fin.first v13) (Fin.second v13)).symm]

/-- Bridge: 3-bidder bidder-3 expected utility under truthful equals
    the analogous bidder-1 expected utility. -/
theorem vickreyBidder3ExpectedUtility3_eq_vickreyExpectedUtility3_truthful
    (n : Nat) (v : Fin n) (prior : Fin (n * n) → Rat) :
    vickreyBidder3ExpectedUtility3 n (fun v => v) (fun v => v) (fun v => v)
                                     v prior
    = vickreyExpectedUtility3 n (fun v => v) (fun v => v) (fun v => v)
                                v prior := by
  unfold vickreyBidder3ExpectedUtility3 vickreyExpectedUtility3
  congr 1
  funext v12
  rw [show (((vickreyBidder3Util3 n v (Fin.first v12) (Fin.second v12)
                                       v).val : Nat) : Rat)
        = (((vickreyUtility3 n v v (Fin.first v12)
                                    (Fin.second v12)).val : Nat) : Rat)
        from by
        exact_mod_cast
          (vickreyUtility3_val_eq_vickreyBidder3Util3_val_truthful n v
            (Fin.first v12) (Fin.second v12)).symm]

/-- **3-bidder pipeline-level Vickrey symmetry**: under truthful
    `spsb3Auction n`, all three bidders have equal expected pipeline
    utility at every common valuation. -/
theorem spsb3Auction_pipeline_utility_symmetric (n : Nat)
    (prior : Fin (n * n) → Rat) (v : Fin n) :
    auctionExpectedBidder1Util3 n (spsb3Auction n) prior v
    = auctionExpectedBidder2Util3 n (spsb3Auction n) prior v
    ∧ auctionExpectedBidder1Util3 n (spsb3Auction n) prior v
    = auctionExpectedBidder3Util3 n (spsb3Auction n) prior v := by
  refine ⟨?_, ?_⟩
  · rw [auctionExpectedBidder1Util3_spsb3Auction_eq,
        auctionExpectedBidder2Util3_spsb3Auction_eq,
        vickreyBidder2ExpectedUtility3_eq_vickreyExpectedUtility3_truthful]
  · rw [auctionExpectedBidder1Util3_spsb3Auction_eq,
        auctionExpectedBidder3Util3_spsb3Auction_eq,
        vickreyBidder3ExpectedUtility3_eq_vickreyExpectedUtility3_truthful]

/-- **Kernel ↔ pipeline consistency (3 bidders)**: kernel-level
    `IsBayesNashVickrey3` for truthful-truthful-truthful is equivalent
    to pipeline-level `IsTruthfulPipelineBayesNashSpsb3Auction`. -/
theorem IsBayesNashVickrey3_iff_pipeline_truthful (n : Nat)
    (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    IsBayesNashVickrey3 n (fun v => v) (fun v => v) (fun v => v)
                          prior23 prior13 prior12
    ↔ IsTruthfulPipelineBayesNashSpsb3Auction n prior23 prior13 prior12 := by
  refine ⟨fun _ => spsb3Auction_truthful_is_pipeline_bayes_nash n
                     prior23 prior13 prior12 h_nn23 h_nn13 h_nn12,
          fun _ => vickrey3_truthful_is_bayes_nash n
                     prior23 prior13 prior12 h_nn23 h_nn13 h_nn12⟩

/-! ## 3-bidder reserve pipeline Bayes-Nash (full BN, all 3 bidders) -/

/-- Bidder 2's expected utility in a 3-bidder reserve auction. -/
def vickreyReserveBidder2ExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v2 : Fin n)
    (p13 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v13 : Fin (n * n) =>
    p13 v13 *
      ((vickreyReserveBidder2Util3 n v2 (s1 (Fin.first v13)) (s2 v2)
                                       (s3 (Fin.second v13)) r).val
              : Nat).cast)

/-- Bidder 3's expected utility in a 3-bidder reserve auction. -/
def vickreyReserveBidder3ExpectedUtility3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (v3 : Fin n)
    (p12 : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v12 : Fin (n * n) =>
    p12 v12 *
      ((vickreyReserveBidder3Util3 n v3 (s1 (Fin.first v12))
                                       (s2 (Fin.second v12)) (s3 v3) r).val
              : Nat).cast)

/-- Bidder 2's truthful best response under 3-bidder reserve. -/
theorem vickreyReserve3_bidder2_truthful_best_response (n : Nat) (r : Fin n)
    (s1 s2' s3 : Fin n → Fin n) (p13 : Fin (n * n) → Rat)
    (h_nn : ∀ v13, 0 ≤ p13 v13) (v2 : Fin n) :
    vickreyReserveBidder2ExpectedUtility3 n r s1 (fun v => v) s3 v2 p13
    ≥ vickreyReserveBidder2ExpectedUtility3 n r s1 s2' s3 v2 p13 := by
  unfold vickreyReserveBidder2ExpectedUtility3
  apply Fin.sumRat_le_local
  intro v13
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v13)
  have := vickreyReserve3_bidder2_truthful_dominant n v2
            (s1 (Fin.first v13)) (s2' v2) (s3 (Fin.second v13)) r
  exact_mod_cast this

/-- Bidder 3's truthful best response under 3-bidder reserve. -/
theorem vickreyReserve3_bidder3_truthful_best_response (n : Nat) (r : Fin n)
    (s1 s2 s3' : Fin n → Fin n) (p12 : Fin (n * n) → Rat)
    (h_nn : ∀ v12, 0 ≤ p12 v12) (v3 : Fin n) :
    vickreyReserveBidder3ExpectedUtility3 n r s1 s2 (fun v => v) v3 p12
    ≥ vickreyReserveBidder3ExpectedUtility3 n r s1 s2 s3' v3 p12 := by
  unfold vickreyReserveBidder3ExpectedUtility3
  apply Fin.sumRat_le_local
  intro v12
  apply Rat.mul_le_mul_of_nonneg_left _ (h_nn v12)
  have := vickreyReserve3_bidder3_truthful_dominant n v3
            (s1 (Fin.first v12)) (s2 (Fin.second v12)) (s3' v3) r
  exact_mod_cast this

/-- Bridge: bidder 2 reserve identity under truthful. -/
theorem vickreyReserveUtility3_val_eq_vickreyReserveBidder2Util3_val_truthful
    (n : Nat) (v opp_b1 opp_b3 r : Fin n) :
    (vickreyReserveUtility3 n v v opp_b1 opp_b3 r).val
    = (vickreyReserveBidder2Util3 n v opp_b1 v opp_b3 r).val := by
  unfold vickreyReserveUtility3 vickreyReserveBidder2Util3
  by_cases hopp : opp_b1.val < v.val
  · by_cases hb3 : v.val ≥ opp_b3.val
    · by_cases hr : v.val ≥ r.val
      · have hge_opp : v.val ≥ opp_b1.val := by omega
        simp [hge_opp, hb3, hr, hopp]
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
          fun ⟨_, _, h⟩ => hr h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
          fun ⟨_, _, h⟩ => hr h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
        fun ⟨_, h, _⟩ => hb3 h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
        fun ⟨_, h, _⟩ => hb3 h
      simp [hnotge, hnotcond]
  · by_cases hge : v.val ≥ opp_b1.val
    · have hveq : v.val = opp_b1.val := by omega
      by_cases hb3 : v.val ≥ opp_b3.val
      · by_cases hr : v.val ≥ r.val
        · simp [hge, hb3, hr, hopp]; omega
        · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
            fun ⟨_, _, h⟩ => hr h
          have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
            fun ⟨_, _, h⟩ => hr h
          simp [hnotge, hnotcond]
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h, _⟩ => hb3 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h, _⟩ => hb3 h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
        fun ⟨h, _, _⟩ => hge h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ v.val ≥ opp_b3.val ∧ v.val ≥ r.val) :=
        fun ⟨h, _, _⟩ => hopp h
      simp [hnotge, hnotcond]

/-- Bridge: bidder 3 reserve identity under truthful. -/
theorem vickreyReserveUtility3_val_eq_vickreyReserveBidder3Util3_val_truthful
    (n : Nat) (v opp_b1 opp_b2 r : Fin n) :
    (vickreyReserveUtility3 n v v opp_b1 opp_b2 r).val
    = (vickreyReserveBidder3Util3 n v opp_b1 opp_b2 v r).val := by
  unfold vickreyReserveUtility3 vickreyReserveBidder3Util3
  by_cases hopp1 : opp_b1.val < v.val
  · by_cases hopp2 : opp_b2.val < v.val
    · by_cases hr : v.val ≥ r.val
      · have hge1 : v.val ≥ opp_b1.val := by omega
        have hge2 : v.val ≥ opp_b2.val := by omega
        simp [hge1, hge2, hr, hopp1, hopp2]
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
          fun ⟨_, _, h⟩ => hr h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
          fun ⟨_, _, h⟩ => hr h
        simp [hnotge, hnotcond]
    · by_cases hge2 : v.val ≥ opp_b2.val
      · have hveq2 : v.val = opp_b2.val := by omega
        by_cases hr : v.val ≥ r.val
        · have hge1 : v.val ≥ opp_b1.val := by omega
          simp [hge1, hge2, hr, hopp1, hopp2]
          omega
        · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
            fun ⟨_, _, h⟩ => hr h
          have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
            fun ⟨_, _, h⟩ => hr h
          simp [hnotge, hnotcond]
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h, _⟩ => hge2 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h, _⟩ => hopp2 h
        simp [hnotge, hnotcond]
  · by_cases hge1 : v.val ≥ opp_b1.val
    · have hveq1 : v.val = opp_b1.val := by omega
      by_cases hge2 : v.val ≥ opp_b2.val
      · by_cases hr : v.val ≥ r.val
        · simp [hge1, hge2, hr, hopp1]
          omega
        · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
            fun ⟨_, _, h⟩ => hr h
          have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
            fun ⟨h, _, _⟩ => hopp1 h
          simp [hnotge, hnotcond]
      · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
          fun ⟨_, h, _⟩ => hge2 h
        have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
          fun ⟨h, _, _⟩ => hopp1 h
        simp [hnotge, hnotcond]
    · have hnotge : ¬ (v.val ≥ opp_b1.val ∧ v.val ≥ opp_b2.val ∧ v.val ≥ r.val) :=
        fun ⟨h, _, _⟩ => hge1 h
      have hnotcond : ¬ (opp_b1.val < v.val ∧ opp_b2.val < v.val ∧ v.val ≥ r.val) :=
        fun ⟨h, _, _⟩ => hopp1 h
      simp [hnotge, hnotcond]

/-- Pipeline ↔ kernel for bidder 2 under truthful spsb3ReserveAuction. -/
theorem auctionExpectedBidder2Util3_spsb3ReserveAuction_eq (n : Nat)
    (r : Fin n) (prior13 : Fin (n * n) → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3ReserveAuction n r) prior13 v2
    = vickreyReserveBidder2ExpectedUtility3 n r (fun v => v) (fun v => v)
                                                (fun v => v) v2 prior13 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder2Util3 vickreyReserveBidder2ExpectedUtility3
  congr 1
  funext v13
  rw [spsb3ReserveAuction_eq_detMatrix, auctionBidder2Util3_det]
  unfold spsb3ReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]
  have hbridge :
      (vickreyReserveUtility3 n v2 v2 (Fin.first v13) (Fin.second v13) r).val
      = (vickreyReserveBidder2Util3 n v2 (Fin.first v13) v2
                                       (Fin.second v13) r).val :=
    vickreyReserveUtility3_val_eq_vickreyReserveBidder2Util3_val_truthful n
      v2 (Fin.first v13) (Fin.second v13) r
  rw [show (((vickreyReserveUtility3 n v2 v2 (Fin.first v13)
                                       (Fin.second v13) r).val : Nat) : Rat)
        = (((vickreyReserveBidder2Util3 n v2 (Fin.first v13) v2
                                       (Fin.second v13) r).val : Nat) : Rat)
        from by exact_mod_cast hbridge]

/-- Pipeline ↔ kernel for bidder 2 under deviator-2 spsb3ReserveAuctionDeviator2. -/
theorem auctionExpectedBidder2Util3_spsb3ReserveAuctionDeviator2_eq (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (prior13 : Fin (n * n) → Rat) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3ReserveAuctionDeviator2 n r bid)
                                   prior13 v2
    = vickreyReserveBidder2ExpectedUtility3 n r (fun v => v) bid
                                                (fun v => v) v2 prior13 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v2.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder2Util3 vickreyReserveBidder2ExpectedUtility3
  congr 1
  funext v13
  rw [spsb3ReserveAuctionDeviator2_eq_detMatrix, auctionBidder2Util3_det]
  unfold spsb3ReserveAuctionDeviator2Fn
  simp only [Fin.first_pair, Fin.second_pair hn, Fin.second_pair hnn]

/-- Pipeline-level bidder-2 BR for spsb3ReserveAuction. -/
theorem spsb3ReserveAuction_bidder2_truthful_best_response_pipeline (n : Nat)
    (r : Fin n) (prior13 : Fin (n * n) → Rat)
    (h_nn : ∀ v, 0 ≤ prior13 v) (bid : Fin n → Fin n) (v2 : Fin n) :
    auctionExpectedBidder2Util3 n (spsb3ReserveAuction n r) prior13 v2
    ≥ auctionExpectedBidder2Util3 n (spsb3ReserveAuctionDeviator2 n r bid)
                                     prior13 v2 := by
  rw [auctionExpectedBidder2Util3_spsb3ReserveAuction_eq,
      auctionExpectedBidder2Util3_spsb3ReserveAuctionDeviator2_eq]
  exact vickreyReserve3_bidder2_truthful_best_response n r (fun v => v) bid
    (fun v => v) prior13 h_nn v2

/-- Pipeline ↔ kernel for bidder 3 under truthful spsb3ReserveAuction. -/
theorem auctionExpectedBidder3Util3_spsb3ReserveAuction_eq (n : Nat)
    (r : Fin n) (prior12 : Fin (n * n) → Rat) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3ReserveAuction n r) prior12 v3
    = vickreyReserveBidder3ExpectedUtility3 n r (fun v => v) (fun v => v)
                                                (fun v => v) v3 prior12 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v3.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder3Util3 vickreyReserveBidder3ExpectedUtility3
  congr 1
  funext v12
  rw [spsb3ReserveAuction_eq_detMatrix, auctionBidder3Util3_det]
  unfold spsb3ReserveAuctionFn
  simp only [Fin.first_pair, Fin.second_pair hnn]
  have hbridge :
      (vickreyReserveUtility3 n v3 v3 (Fin.first v12) (Fin.second v12) r).val
      = (vickreyReserveBidder3Util3 n v3 (Fin.first v12) (Fin.second v12)
                                       v3 r).val :=
    vickreyReserveUtility3_val_eq_vickreyReserveBidder3Util3_val_truthful n
      v3 (Fin.first v12) (Fin.second v12) r
  rw [show (((vickreyReserveUtility3 n v3 v3 (Fin.first v12)
                                       (Fin.second v12) r).val : Nat) : Rat)
        = (((vickreyReserveBidder3Util3 n v3 (Fin.first v12)
                                       (Fin.second v12) v3 r).val : Nat) : Rat)
        from by exact_mod_cast hbridge]

/-- Pipeline ↔ kernel for bidder 3 under deviator-3 spsb3ReserveAuctionDeviator3. -/
theorem auctionExpectedBidder3Util3_spsb3ReserveAuctionDeviator3_eq (n : Nat)
    (r : Fin n) (bid : Fin n → Fin n) (prior12 : Fin (n * n) → Rat) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3ReserveAuctionDeviator3 n r bid)
                                   prior12 v3
    = vickreyReserveBidder3ExpectedUtility3 n r (fun v => v) (fun v => v) bid
                                                v3 prior12 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v3.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  unfold auctionExpectedBidder3Util3 vickreyReserveBidder3ExpectedUtility3
  congr 1
  funext v12
  rw [spsb3ReserveAuctionDeviator3_eq_detMatrix, auctionBidder3Util3_det]
  unfold spsb3ReserveAuctionDeviator3Fn
  simp only [Fin.first_pair, Fin.second_pair hnn]

/-- Pipeline-level bidder-3 BR for spsb3ReserveAuction. -/
theorem spsb3ReserveAuction_bidder3_truthful_best_response_pipeline (n : Nat)
    (r : Fin n) (prior12 : Fin (n * n) → Rat)
    (h_nn : ∀ v, 0 ≤ prior12 v) (bid : Fin n → Fin n) (v3 : Fin n) :
    auctionExpectedBidder3Util3 n (spsb3ReserveAuction n r) prior12 v3
    ≥ auctionExpectedBidder3Util3 n (spsb3ReserveAuctionDeviator3 n r bid)
                                     prior12 v3 := by
  rw [auctionExpectedBidder3Util3_spsb3ReserveAuction_eq,
      auctionExpectedBidder3Util3_spsb3ReserveAuctionDeviator3_eq]
  exact vickreyReserve3_bidder3_truthful_best_response n r (fun v => v)
    (fun v => v) bid prior12 h_nn v3

/-- Pipeline Bayes-Nash equilibrium predicate for 3-bidder spsbReserve. -/
def IsTruthfulPipelineBayesNashSpsb3ReserveAuction (n : Nat) (r : Fin n)
    (prior23 : Fin (n * n) → Rat) (prior13 : Fin (n * n) → Rat)
    (prior12 : Fin (n * n) → Rat) : Prop :=
  (∀ (bid : Fin n → Fin n) (v1 : Fin n),
    auctionExpectedBidder1Util3 n (spsb3ReserveAuction n r) prior23 v1
    ≥ auctionExpectedBidder1Util3 n (spsb3ReserveAuctionDeviator1 n r bid)
                                    prior23 v1)
  ∧
  (∀ (bid : Fin n → Fin n) (v2 : Fin n),
    auctionExpectedBidder2Util3 n (spsb3ReserveAuction n r) prior13 v2
    ≥ auctionExpectedBidder2Util3 n (spsb3ReserveAuctionDeviator2 n r bid)
                                    prior13 v2)
  ∧
  (∀ (bid : Fin n → Fin n) (v3 : Fin n),
    auctionExpectedBidder3Util3 n (spsb3ReserveAuction n r) prior12 v3
    ≥ auctionExpectedBidder3Util3 n (spsb3ReserveAuctionDeviator3 n r bid)
                                    prior12 v3)

/-- **Pipeline-level Bayes-Nash truthfulness for 3-bidder spsbReserve**.
    Truthful-truthful-truthful is a Bayes-Nash equilibrium of the
    OpenGame pipeline form under any priors with nonnegative weights. -/
theorem spsb3ReserveAuction_truthful_is_pipeline_bayes_nash (n : Nat)
    (r : Fin n) (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    IsTruthfulPipelineBayesNashSpsb3ReserveAuction n r prior23 prior13 prior12 :=
  ⟨spsb3ReserveAuction_truthful_best_response_pipeline n r prior23 h_nn23,
   spsb3ReserveAuction_bidder2_truthful_best_response_pipeline n r prior13 h_nn13,
   spsb3ReserveAuction_bidder3_truthful_best_response_pipeline n r prior12 h_nn12⟩

/-- Kernel-level best response under 3-bidder reserve-spsb (bidder 1's POV). -/
def IsBestResponseVickreyReserve3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n) (p23 : Fin (n * n) → Rat) : Prop :=
  ∀ (s1' : Fin n → Fin n) (v1 : Fin n),
    vickreyReserveExpectedUtility3 n r s1 s2 s3 v1 p23
    ≥ vickreyReserveExpectedUtility3 n r s1' s2 s3 v1 p23

/-- Kernel-level Bayes-Nash equilibrium predicate under 3-bidder
    reserve-spsb. -/
def IsBayesNashVickreyReserve3 (n : Nat) (r : Fin n)
    (s1 s2 s3 : Fin n → Fin n)
    (p23 p13 p12 : Fin (n * n) → Rat) : Prop :=
  IsBestResponseVickreyReserve3 n r s1 s2 s3 p23
  ∧ IsBestResponseVickreyReserve3 n r s2 s1 s3 p13
  ∧ IsBestResponseVickreyReserve3 n r s3 s1 s2 p12

/-- Truthful-truthful-truthful is a kernel-level Bayes-Nash
    equilibrium of 3-bidder reserve-spsb. -/
theorem vickreyReserve3_truthful_is_bayes_nash (n : Nat) (r : Fin n)
    (p23 p13 p12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ p23 v) (h_nn13 : ∀ v, 0 ≤ p13 v)
    (h_nn12 : ∀ v, 0 ≤ p12 v) :
    IsBayesNashVickreyReserve3 n r (fun v => v) (fun v => v) (fun v => v)
                                    p23 p13 p12 :=
  ⟨fun s1' v1 => vickreyReserve3_truthful_best_response n r s1' (fun v => v)
                  (fun v => v) p23 h_nn23 v1,
   fun s2' v2 => vickreyReserve3_truthful_best_response n r s2' (fun v => v)
                  (fun v => v) p13 h_nn13 v2,
   fun s3' v3 => vickreyReserve3_truthful_best_response n r s3' (fun v => v)
                  (fun v => v) p12 h_nn12 v3⟩

/-- **Kernel ↔ pipeline consistency (3-bidder reserve)**. -/
theorem IsBayesNashVickreyReserve3_iff_pipeline_truthful (n : Nat) (r : Fin n)
    (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    IsBayesNashVickreyReserve3 n r (fun v => v) (fun v => v) (fun v => v)
                                  prior23 prior13 prior12
    ↔ IsTruthfulPipelineBayesNashSpsb3ReserveAuction n r prior23 prior13 prior12 := by
  refine ⟨fun _ => spsb3ReserveAuction_truthful_is_pipeline_bayes_nash n r
                     prior23 prior13 prior12 h_nn23 h_nn13 h_nn12,
          fun _ => vickreyReserve3_truthful_is_bayes_nash n r prior23 prior13
                     prior12 h_nn23 h_nn13 h_nn12⟩

/-! ## Concrete pipeline computations at small `n`

  Demonstrate that the pipeline framework reduces to concrete
  numerical values via the `_eq` bridges to kernel forms. -/

/-- At `n = 2` with uniform prior `1/2`, bidder 1 with valuation `1`
    in truthful spsbAuction has expected pipeline utility `1/2`:
    half the time bidder 2 has `v2 = 0` (winning utility = 1 - 0 = 1),
    half the time `v2 = 1` (tied, no positive surplus). -/
example :
    auctionExpectedBidder1Util 2 (spsbAuction 2)
        (fun _ => (1 : Rat) / 2) ⟨1, by decide⟩
    = 1 / 2 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq]
  unfold vickreyExpectedUtility
  native_decide

/-- At `n = 2` with uniform prior `1/2`, bidder 1 with valuation `0`
    in truthful spsbAuction has expected pipeline utility `0`. -/
example :
    auctionExpectedBidder1Util 2 (spsbAuction 2)
        (fun _ => (1 : Rat) / 2) ⟨0, by decide⟩
    = 0 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq]
  unfold vickreyExpectedUtility
  native_decide

/-- At `n = 3` with uniform prior `1/3`, bidder 1 with valuation `2`
    in truthful spsbAuction has expected pipeline utility `1`:
    averaged over `v2 ∈ {0, 1, 2}`, the surplus `2 - v2` is
    `(2 + 1 + 0)/3 = 1`. -/
example :
    auctionExpectedBidder1Util 3 (spsbAuction 3)
        (fun _ => (1 : Rat) / 3) ⟨2, by decide⟩
    = 1 := by
  rw [auctionExpectedBidder1Util_spsbAuction_eq]
  unfold vickreyExpectedUtility
  native_decide

/-- Bidder-2 symmetric: at `n = 2` with uniform prior `1/2`,
    bidder 2 with valuation `1` in truthful spsbAuction has expected
    pipeline utility `0` because bidder 2 loses ties to bidder 1.
    With `v1 = 0`: bidder 2 wins (1 > 0), pays 0, utility = 1.
    With `v1 = 1`: tie, bidder 2 loses (utility = 0).
    Sum: `(1/2)·1 + (1/2)·0 = 1/2`.  Same as bidder 1's by symmetry. -/
example :
    auctionExpectedBidder2Util 2 (spsbAuction 2)
        (fun _ => (1 : Rat) / 2) ⟨1, by decide⟩
    = 1 / 2 := by
  rw [auctionExpectedBidder2Util_spsbAuction_eq]
  unfold vickreyBidder2ExpectedUtility
  native_decide

/-- Reserve example: at `n = 4` with uniform prior `1/4` and reserve
    `r = 2`, bidder 1 with valuation `3` in truthful spsbReserveAuction
    has expected pipeline utility = `1/4`.

    Computation: bidder 1 wins iff `v1 ≥ v2 ∧ v1 ≥ r` (= `v1 ≥ 2`,
    holds since `v1 = 3`).  Payment = `max r v2` = `max 2 v2`.
    For `v2 ∈ {0, 1, 2, 3}`: payments `(2, 2, 2, 2)` → surpluses
    `(1, 1, 1, 0)` → sum = 3 → expected = `3/4`.  Wait, must
    handle the tie case `v1 = v2 = 3`: bidder 1 still wins (weak
    inequality), pays `max 2 3 = 3`, surplus = 0.  Other cases:
    `v2 < 3`, bidder 1 wins, pays `max 2 v2`.  `v2 = 0`: pays 2, surplus 1.
    `v2 = 1`: pays 2, surplus 1.  `v2 = 2`: pays 2, surplus 1.
    Sum = `(1 + 1 + 1 + 0)/4 = 3/4`. -/
example :
    auctionExpectedBidder1Util 4 (spsbReserveAuction 4 ⟨2, by decide⟩)
        (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩
    = 3 / 4 := by
  rw [auctionExpectedBidder1Util_spsbReserveAuction_eq]
  unfold vickreyReserveExpectedUtility
  native_decide

/-- 3-bidder example: at `n = 3` with uniform joint prior `1/9` over
    `(v2, v3)`, bidder 1 with the top valuation `v1 = 2` in truthful
    spsb3Auction has expected pipeline utility = `5/9`.

    Bidder 1 always wins (top type).  Pays `max v2 v3`.  Surplus
    `2 - max(v2, v3)` summed over the 9 (v2, v3) pairs:
    `2 + 1 + 0 + 1 + 1 + 0 + 0 + 0 + 0 = 5`.
    Expected = `5/9`. -/
example :
    auctionExpectedBidder1Util3 3 (spsb3Auction 3)
        (fun _ => (1 : Rat) / 9) ⟨2, by decide⟩
    = 5 / 9 := by
  rw [auctionExpectedBidder1Util3_spsb3Auction_eq]
  unfold vickreyExpectedUtility3
  native_decide

/-- 3-bidder bidder-2 example: at `n = 3` with uniform joint prior `1/9`
    over `(v1, v3)`, bidder 2 with the top valuation `v2 = 2` in
    truthful spsb3Auction has expected pipeline utility = `5/9` (by
    symmetry with bidder 1's case). -/
example :
    auctionExpectedBidder2Util3 3 (spsb3Auction 3)
        (fun _ => (1 : Rat) / 9) ⟨2, by decide⟩
    = 5 / 9 := by
  rw [auctionExpectedBidder2Util3_spsb3Auction_eq]
  unfold vickreyBidder2ExpectedUtility3
  native_decide

/-- 3-bidder bidder-3 example: at `n = 3` with uniform joint prior `1/9`
    over `(v1, v2)`, bidder 3 with the top valuation `v3 = 2` in
    truthful spsb3Auction has expected pipeline utility `5/9`.

    Bidder 3 wins iff `v1 < 2 ∧ v2 < 2` (strict tie-loss), i.e., on
    the 4 pairs `{(0,0), (0,1), (1,0), (1,1)}` with respective
    surpluses `(2, 1, 1, 1)`; the other 5 pairs (where `v1 = 2` or
    `v2 = 2`) give 0.  Sum = `5`, expected = `5/9`. -/
example :
    auctionExpectedBidder3Util3 3 (spsb3Auction 3)
        (fun _ => (1 : Rat) / 9) ⟨2, by decide⟩
    = 5 / 9 := by
  rw [auctionExpectedBidder3Util3_spsb3Auction_eq]
  unfold vickreyBidder3ExpectedUtility3
  native_decide

/-- Envelope-integral example: at `n = 4` with uniform prior `1/4`,
    bidder 1 with valuation `3` in truthful spsbAuction has expected
    pipeline utility `3/2`, which equals the Myerson envelope
    integral `Σ_{t < 3} vickreyAllocation t = 1/4 + 1/2 + 3/4 = 3/2`. -/
example :
    auctionExpectedBidder1Util 4 (spsbAuction 4)
        (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩
    = vickreyEnvelopeIntegral 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩ :=
  auctionExpectedBidder1Util_spsbAuction_eq_envelopeIntegral 4
    (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩

/-- The envelope-integral side computes to `3/2`. -/
example :
    vickreyEnvelopeIntegral 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩
    = 3 / 2 := by
  unfold vickreyEnvelopeIntegral vickreyAllocation
  native_decide

/-- Vickrey-symmetry example via the symmetry theorem: bidder 1 and
    bidder 2 have equal expected pipeline utility at `v = 1` (both
    1/2 from the earlier concrete examples). -/
example :
    auctionExpectedBidder1Util 2 (spsbAuction 2)
        (fun _ => (1 : Rat) / 2) ⟨1, by decide⟩
    = auctionExpectedBidder2Util 2 (spsbAuction 2)
        (fun _ => (1 : Rat) / 2) ⟨1, by decide⟩ :=
  spsbAuction_pipeline_utility_symmetric 2 (fun _ => (1 : Rat) / 2)
    ⟨1, by decide⟩

/-! ## Main pipeline-level results (summary)

  Consolidates the key Vickrey pipeline theorems for `spsbAuction n`:
  pipeline ↔ closed-form, pipeline ↔ envelope integral, and the
  truthful-truthful Bayes-Nash equilibrium. -/

/-- **Pipeline-level RET (revenue equivalence via envelope)**.
    Any auction whose expected pipeline utility equals the Myerson
    envelope integral has the same expected pipeline utility as
    `spsbAuction n` at every type.  This is the "envelope side" of
    Myerson's RET: same envelope integral → same utility profile. -/
theorem pipeline_RET_via_envelope (n : Nat)
    (auction : StochasticMatrix (n * n) (n * n))
    (prior : Fin n → Rat)
    (h_env : ∀ v1, auctionExpectedBidder1Util n auction prior v1
                  = vickreyEnvelopeIntegral n prior v1) (v1 : Fin n) :
    auctionExpectedBidder1Util n auction prior v1
    = auctionExpectedBidder1Util n (spsbAuction n) prior v1 := by
  rw [h_env, auctionExpectedBidder1Util_spsbAuction_eq_envelopeIntegral]

/-- **Pipeline-level RET (bidder 2)**.  Symmetric to bidder 1: any
    auction whose expected bidder-2 pipeline utility equals the
    Myerson envelope integral has the same expected pipeline utility
    as `spsbAuction n`. -/
theorem pipeline_RET_via_envelope_bidder2 (n : Nat)
    (auction : StochasticMatrix (n * n) (n * n))
    (prior : Fin n → Rat)
    (h_env : ∀ v2, auctionExpectedBidder2Util n auction prior v2
                  = vickreyEnvelopeIntegral n prior v2) (v2 : Fin n) :
    auctionExpectedBidder2Util n auction prior v2
    = auctionExpectedBidder2Util n (spsbAuction n) prior v2 := by
  rw [h_env, auctionExpectedBidder2Util_spsbAuction_eq_envelopeIntegral]

/-- **Main pipeline Vickrey theorem** (2-bidder).  For `spsbAuction n`
    under any prior with nonnegative weights:

    1. The pipeline reduces to `detMatrix (spsbAuctionFn n)`.
    2. Bidder 1's expected pipeline utility equals the Myerson
       envelope integral of the Vickrey allocation rule.
    3. Truthful-truthful is a Bayes-Nash equilibrium. -/
theorem spsbAuction_main_pipeline_results (n : Nat) (prior : Fin n → Rat)
    (h_nn : ∀ v, 0 ≤ prior v) :
    spsbAuction n = detMatrix (spsbAuctionFn n)
    ∧ (∀ v1, auctionExpectedBidder1Util n (spsbAuction n) prior v1
              = vickreyEnvelopeIntegral n prior v1)
    ∧ IsTruthfulPipelineBayesNashSpsbAuction n prior :=
  ⟨spsbAuction_eq_detMatrix n,
   auctionExpectedBidder1Util_spsbAuction_eq_envelopeIntegral n prior,
   spsbAuction_truthful_is_pipeline_bayes_nash n prior h_nn⟩

/-- **Main pipeline Vickrey-with-reserve theorem** (2-bidder).  For
    `spsbReserveAuction n r`:

    1. The pipeline reduces to `detMatrix (spsbReserveAuctionFn n r)`.
    2. Bidder 1's expected pipeline utility equals
       `vickreyReserveEqUtility n r prior`.
    3. Truthful-truthful is a Bayes-Nash equilibrium. -/
theorem spsbReserveAuction_main_pipeline_results (n : Nat) (r : Fin n)
    (prior : Fin n → Rat) (h_nn : ∀ v, 0 ≤ prior v) :
    spsbReserveAuction n r = detMatrix (spsbReserveAuctionFn n r)
    ∧ (∀ v1, auctionExpectedBidder1Util n (spsbReserveAuction n r) prior v1
              = vickreyReserveEqUtility n r prior v1)
    ∧ IsTruthfulPipelineBayesNashSpsbReserveAuction n r prior :=
  ⟨spsbReserveAuction_eq_detMatrix n r,
   auctionExpectedBidder1Util_spsbReserveAuction_eq_vickreyReserveEqUtility n r prior,
   spsbReserveAuction_truthful_is_pipeline_bayes_nash n r prior h_nn⟩

/-- **Main pipeline Vickrey theorem** (3-bidder).  For `spsb3Auction n`:

    1. The pipeline reduces to `detMatrix (spsbAuctionFn3 n)`.
    2. Truthful-truthful-truthful is a Bayes-Nash equilibrium under
       any independent priors on the other bidders' valuations. -/
theorem spsb3Auction_main_pipeline_results (n : Nat)
    (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    spsb3Auction n = detMatrix (spsbAuctionFn3 n)
    ∧ IsTruthfulPipelineBayesNashSpsb3Auction n prior23 prior13 prior12 :=
  ⟨spsb3Auction_eq_detMatrix n,
   spsb3Auction_truthful_is_pipeline_bayes_nash n prior23 prior13 prior12
     h_nn23 h_nn13 h_nn12⟩

/-- **Main pipeline Vickrey-with-reserve theorem** (3-bidder).  For
    `spsb3ReserveAuction n r`:

    1. The pipeline reduces to `detMatrix (spsb3ReserveAuctionFn n r)`.
    2. Truthful-truthful-truthful is a Bayes-Nash equilibrium. -/
theorem spsb3ReserveAuction_main_pipeline_results (n : Nat) (r : Fin n)
    (prior23 prior13 prior12 : Fin (n * n) → Rat)
    (h_nn23 : ∀ v, 0 ≤ prior23 v) (h_nn13 : ∀ v, 0 ≤ prior13 v)
    (h_nn12 : ∀ v, 0 ≤ prior12 v) :
    spsb3ReserveAuction n r = detMatrix (spsb3ReserveAuctionFn n r)
    ∧ IsTruthfulPipelineBayesNashSpsb3ReserveAuction n r prior23 prior13 prior12 :=
  ⟨spsb3ReserveAuction_eq_detMatrix n r,
   spsb3ReserveAuction_truthful_is_pipeline_bayes_nash n r prior23 prior13 prior12
     h_nn23 h_nn13 h_nn12⟩

end AuctionCat
