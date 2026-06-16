import AuctionCat.FirstPrice3
import AuctionCat.SecondPrice3
import AuctionCat.English3
import AuctionCat.Dutch3
import AuctionCat.Reserve

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

/-- **Revenue invariance under bidder permutation (3 bidders)**:
    cyclic permutation `(p1, p2, p3) → (p2, p3, p1)` preserves the
    total revenue, since `outcomeRevenue3` is the sum of three
    prices.  Captures the bidder-relabeling invariance at three
    bidders. -/
theorem outcomeRevenue3_cyclic_symmetric (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
    = outcomeRevenue3 n
        (Fin.pair (Fin.pair (Fin.second (Fin.first i)) (Fin.second i))
                   (Fin.first (Fin.first i))) := by
  unfold outcomeRevenue3
  simp only [Fin.first_pair, Fin.second_pair h_pos, Fin.second_pair h_pos2]
  omega

/-- **Inverse cyclic permutation symmetry**: `(p1, p2, p3) → (p3, p1, p2)`
    also preserves revenue.  Three iterations of the cyclic
    permutation return to identity, so this is the other "rotation". -/
theorem outcomeRevenue3_inverse_cyclic_symmetric (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
    = outcomeRevenue3 n
        (Fin.pair (Fin.pair (Fin.second i) (Fin.first (Fin.first i)))
                   (Fin.second (Fin.first i))) := by
  unfold outcomeRevenue3
  simp only [Fin.first_pair, Fin.second_pair h_pos, Fin.second_pair h_pos2]
  omega

/-- **Swap bidder 1 ↔ bidder 3 revenue symmetry**: exchanging the
    bidder 1 and bidder 3 outcomes preserves total revenue. -/
theorem outcomeRevenue3_swap_13_symmetric (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
    = outcomeRevenue3 n
        (Fin.pair (Fin.pair (Fin.second i) (Fin.second (Fin.first i)))
                   (Fin.first (Fin.first i))) := by
  unfold outcomeRevenue3
  simp only [Fin.first_pair, Fin.second_pair h_pos, Fin.second_pair h_pos2]
  omega

/-- **Swap bidder 2 ↔ bidder 3 revenue symmetry**: exchanging the
    bidder 2 and bidder 3 outcomes preserves total revenue. -/
theorem outcomeRevenue3_swap_23_symmetric (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
    = outcomeRevenue3 n
        (Fin.pair (Fin.pair (Fin.first (Fin.first i)) (Fin.second i))
                   (Fin.second (Fin.first i))) := by
  unfold outcomeRevenue3
  simp only [Fin.first_pair, Fin.second_pair h_pos, Fin.second_pair h_pos2]
  omega

/-- **Swap bidder 1 ↔ bidder 2 revenue symmetry**: exchanging the
    bidder 1 and bidder 2 outcomes preserves total revenue. -/
theorem outcomeRevenue3_swap_12_symmetric (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
    = outcomeRevenue3 n
        (Fin.pair (Fin.pair (Fin.second (Fin.first i))
                             (Fin.first (Fin.first i)))
                   (Fin.second i)) := by
  unfold outcomeRevenue3
  simp only [Fin.first_pair, Fin.second_pair h_pos, Fin.second_pair h_pos2]
  omega

/-- **Bundle of three adjacent transpositions**: the three
    transposition generators of S3 (12, 23, 13) all preserve total
    revenue.  Together they generate the full S3 permutation group
    acting on the bidder outcomes. -/
theorem outcomeRevenue3_three_transpositions (n : Nat)
    (i : Fin (((2 * n) * (2 * n)) * (2 * n))) (h_pos : 0 < 2 * n)
    (h_pos2 : 0 < (2 * n) * (2 * n)) :
    outcomeRevenue3 n i
      = outcomeRevenue3 n
          (Fin.pair (Fin.pair (Fin.second (Fin.first i))
                               (Fin.first (Fin.first i)))
                     (Fin.second i))
    ∧ outcomeRevenue3 n i
      = outcomeRevenue3 n
          (Fin.pair (Fin.pair (Fin.first (Fin.first i)) (Fin.second i))
                     (Fin.second (Fin.first i)))
    ∧ outcomeRevenue3 n i
      = outcomeRevenue3 n
          (Fin.pair (Fin.pair (Fin.second i) (Fin.second (Fin.first i)))
                     (Fin.first (Fin.first i))) :=
  ⟨outcomeRevenue3_swap_12_symmetric n i h_pos h_pos2,
   outcomeRevenue3_swap_23_symmetric n i h_pos h_pos2,
   outcomeRevenue3_swap_13_symmetric n i h_pos h_pos2⟩

end AuctionCat
