import AuctionCat.FirstPrice3
import AuctionCat.SecondPrice3
import AuctionCat.English3
import AuctionCat.Dutch3

/-!
# AuctionCat.Revenue3

Revenue framework for three-bidder auctions.

Parallels `AuctionCat.Revenue` for two bidders, with the per-outcome
and per-mechanism functions generalised to the three-bidder type
shape:

  Input  : `Fin ((n * n) * n)`              (joint valuations / bids)
  Output : `Fin (((2 * n) * (2 * n)) * (2 * n))` (joint outcomes)

The framework supports stating revenue equivalence between any two
three-bidder mechanisms under a common prior over joint valuations.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The total payment in a three-bidder auction outcome. -/
def outcomeRevenue3 (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) : Nat :=
  let o1 := Fin.first (Fin.first i)
  let o2 := Fin.second (Fin.first i)
  let o3 := Fin.second i
  let p1 := Fin.second o1
  let p2 := Fin.second o2
  let p3 := Fin.second o3
  p1.val + p2.val + p3.val

/-- The expected total revenue of a three-bidder mechanism `M` under
    a prior over joint valuations. -/
def expectedRevenue3 (n : Nat)
    (M : StochasticMatrix ((n * n) * n) (((2 * n) * (2 * n)) * (2 * n)))
    (prior : Fin ((n * n) * n) → Rat) : Rat :=
  Fin.sumRat (fun v : Fin ((n * n) * n) =>
    prior v
    * Fin.sumRat (fun o : Fin (((2 * n) * (2 * n)) * (2 * n)) =>
        M.entry v o * (outcomeRevenue3 n o : Nat).cast))

/-- Two three-bidder mechanisms are *revenue equivalent under
    `prior`* iff their expected revenues agree. -/
def IsRevenueEquivalent3 (n : Nat)
    (M1 M2 : StochasticMatrix ((n * n) * n)
              (((2 * n) * (2 * n)) * (2 * n)))
    (prior : Fin ((n * n) * n) → Rat) : Prop :=
  expectedRevenue3 n M1 prior = expectedRevenue3 n M2 prior

/-- The uniform prior over three-bidder joint valuations
    `Fin ((n * n) * n)`. -/
def uniformPrior3 (n : Nat) : Fin ((n * n) * n) → Rat :=
  fun _ => 1 / ((((n * n) * n : Nat)) : Rat)

/-! ## Concrete revenue verifications at three bidders

  Three bidders with binary valuations `Fin 2` and uniform prior.
  Under truthful bidding:

    spsb3: winner pays max(others' bids) — revenue = 1/2.
    fpsb3: winner pays own bid           — revenue = 7/8.

  These illustrate the per-mechanism revenue computation and confirm
  that truthful is NOT a revenue-equivalent baseline for first-price
  (which is correct: truthful is not the equilibrium for fpsb). -/

/-- Second-price-sealed-bid (Vickrey) at three bidders, `X = 2`,
    uniform prior, truthful bidding: expected revenue = 1/2. -/
example :
    expectedRevenue3 2 (secondPriceSealedBid3 2) (uniformPrior3 2) = 1 / 2 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- First-price-sealed-bid at three bidders, `X = 2`, uniform prior,
    truthful bidding: expected revenue = 7/8.  (Not equivalent to
    spsb under truthful — first-price equilibrium would shade.) -/
example :
    expectedRevenue3 2 (firstPriceSealedBid3 2) (uniformPrior3 2) = 7 / 8 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- Trivially, every three-bidder mechanism is revenue equivalent to
    itself under any prior. -/
example (n : Nat)
    (M : StochasticMatrix ((n * n) * n) (((2 * n) * (2 * n)) * (2 * n)))
    (prior : Fin ((n * n) * n) → Rat) :
    IsRevenueEquivalent3 n M M prior := rfl

/-- Reflexivity: every three-bidder mechanism is revenue equivalent to
    itself. -/
theorem IsRevenueEquivalent3.refl' {n : Nat}
    (M : StochasticMatrix ((n * n) * n) (((2 * n) * (2 * n)) * (2 * n)))
    (prior : Fin ((n * n) * n) → Rat) :
    IsRevenueEquivalent3 n M M prior :=
  Eq.refl _

/-- Symmetry of the three-bidder revenue-equivalence relation. -/
theorem IsRevenueEquivalent3.symm' {n : Nat}
    {M1 M2 : StochasticMatrix ((n * n) * n)
              (((2 * n) * (2 * n)) * (2 * n))}
    {prior : Fin ((n * n) * n) → Rat}
    (h : IsRevenueEquivalent3 n M1 M2 prior) :
    IsRevenueEquivalent3 n M2 M1 prior :=
  h.symm

/-- Transitivity of the three-bidder revenue-equivalence relation. -/
theorem IsRevenueEquivalent3.trans' {n : Nat}
    {M1 M2 M3 : StochasticMatrix ((n * n) * n)
                  (((2 * n) * (2 * n)) * (2 * n))}
    {prior : Fin ((n * n) * n) → Rat}
    (h12 : IsRevenueEquivalent3 n M1 M2 prior)
    (h23 : IsRevenueEquivalent3 n M2 M3 prior) :
    IsRevenueEquivalent3 n M1 M3 prior :=
  h12.trans h23

/-! ## Strategic-equivalence revenue corollaries (3 bidders)

  English3 ≅ SecondPriceSealedBid3 and Dutch3 ≅ FirstPriceSealedBid3
  at the mechanism level (kernel rfl), so their expected revenues
  match trivially under any prior at three bidders. -/

/-- Three-bidder English has the same expected revenue as Vickrey
    under any prior — corollary of `english3_eq_secondPrice3`. -/
theorem english3_revenue_eq_spsb3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (englishAuction3 n) prior
    = expectedRevenue3 n (secondPriceSealedBid3 n) prior := rfl

/-- Three-bidder Dutch has the same expected revenue as first-price
    sealed-bid under any prior — corollary of `dutch3_eq_firstPrice3`. -/
theorem dutch3_revenue_eq_fpsb3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    expectedRevenue3 n (dutchAuction3 n) prior
    = expectedRevenue3 n (firstPriceSealedBid3 n) prior := rfl

/-- English3 ≅ SPSB3 revenue equivalence as an inhabitant of the
    `IsRevenueEquivalent3` relation. -/
theorem english3_is_revenue_equivalent_spsb3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    IsRevenueEquivalent3 n (englishAuction3 n)
                            (secondPriceSealedBid3 n) prior :=
  rfl

/-- Dutch3 ≅ FPSB3 revenue equivalence as an inhabitant of the
    `IsRevenueEquivalent3` relation. -/
theorem dutch3_is_revenue_equivalent_fpsb3 (n : Nat)
    (prior : Fin ((n * n) * n) → Rat) :
    IsRevenueEquivalent3 n (dutchAuction3 n)
                            (firstPriceSealedBid3 n) prior :=
  rfl

/-! ## Pointwise revenue comparison at three bidders

  Under truthful bidding, three-bidder first-price extracts the
  highest bid (= valuation) as revenue, while three-bidder
  second-price extracts the second-highest bid.  Hence at every
  joint-valuation input, the first-price revenue is weakly greater
  than the second-price revenue.  This is the discrete analogue of
  the standard "fpsb yields higher revenue than spsb pointwise under
  truthful play" observation. -/

/-- Pointwise revenue comparison at three bidders: first-price ≥
    second-price at every joint-bid input.  Both formats put exactly
    one bidder paying (the winner); for fpsb that is the winner's own
    bid (= max), for spsb it is the max of the other two bids (=
    second-max), so the inequality follows by case analysis on which
    bidder wins. -/
theorem fpsb3_revenue_ge_spsb3 (n : Nat) (i : Fin (n * n * n)) :
    outcomeRevenue3 n (fpsb3Fn n i) ≥ outcomeRevenue3 n (spsb3Fn n i) := by
  have hnnn : 0 < n * n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue3 fpsb3Fn spsb3Fn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw1 :
      (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
  · simp [hw1]
  · simp [hw1]
    by_cases hw2 : (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
    · simp [hw2]
      omega
    · simp [hw2]
      omega

/-- Closed-form fpsb3 revenue: at every joint bid `i`, the
    three-bidder first-price revenue equals the maximum of the three
    bids.  Winner-pays-own-bid rule as a three-way `max`. -/
theorem fpsb3_revenue_eq_max (n : Nat) (i : Fin (n * n * n)) :
    outcomeRevenue3 n (fpsb3Fn n i)
    = max (Fin.first (Fin.first i)).val
        (max (Fin.second (Fin.first i)).val (Fin.second i).val) := by
  have hnnn : 0 < n * n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue3 fpsb3Fn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw1 :
      (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
  · simp [hw1]; omega
  · simp [hw1]
    by_cases hw2 : (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
    · simp [hw2]; omega
    · simp [hw2]; omega

/-- Closed-form spsb3 revenue: at every joint bid `i`, the
    three-bidder second-price (Vickrey) revenue equals the
    second-highest of the three bids, expressed as
    `max (min b1 b2) (max (min b1 b3) (min b2 b3))`. -/
theorem spsb3_revenue_eq_second_max (n : Nat) (i : Fin (n * n * n)) :
    outcomeRevenue3 n (spsb3Fn n i)
    = max (min (Fin.first (Fin.first i)).val
               (Fin.second (Fin.first i)).val)
          (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
               (min (Fin.second (Fin.first i)).val (Fin.second i).val)) := by
  have hnnn : 0 < n * n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue3 spsb3Fn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw1 :
      (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
  · simp [hw1]; omega
  · simp [hw1]
    by_cases hw2 : (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
    · simp [hw2]; omega
    · simp [hw2]; omega

end AuctionCat
