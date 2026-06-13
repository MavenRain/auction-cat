import AuctionCat.FirstPrice
import AuctionCat.SecondPrice
import AuctionCat.English
import AuctionCat.Dutch

/-!
# AuctionCat.Revenue

Revenue analysis for two-bidder auctions.

The standard result (Myerson 1981, *Optimal Auction Design*) is the
**Revenue Equivalence Theorem**: in an independent-private-values
setting with symmetric risk-neutral bidders playing symmetric
Bayes-Nash equilibrium, all auction formats that

  - allocate the object to the bidder with the highest valuation,
  - give zero expected surplus to the lowest type,

yield the same expected revenue.  In particular, first-price-sealed-
bid, second-price-sealed-bid (Vickrey), Dutch, and English auctions
all give the same expected revenue when bidders use their respective
equilibrium strategies.

This file lays the framework for that statement:

  outcomeRevenue n o
    The total payment extracted in a single outcome (sum of all
    bidders' prices).

  expectedRevenue n M prior
    The expected total revenue when bids are drawn from `prior` and
    the mechanism `M` produces outcomes.

The full revenue-equivalence theorem requires the envelope-theorem
machinery for Bayesian games (translating between bidding strategies
under different formats) and is left for a follow-on once that
infrastructure is in place.  This file provides the data layer; the
equilibrium-strategy and envelope-theorem layers come on top.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The total payment in a two-bidder auction outcome.

    Input: `i : Fin ((2 * n) * (2 * n))` decodes to
      `(o₁, o₂)` where `oᵢ : Fin (2 * n)` is bidder `i`'s
      `(allocation, price)` pair.

    Output: `p₁ + p₂` as a Nat (no Fin bound — sum may exceed
    `n - 1` in formats where multiple bidders pay simultaneously,
    even though the standard formats here have at most one paying
    bidder per outcome). -/
def outcomeRevenue (n : Nat) (i : Fin ((2 * n) * (2 * n))) : Nat :=
  let o1 := Fin.first i
  let o2 := Fin.second i
  let p1 := Fin.second o1
  let p2 := Fin.second o2
  p1.val + p2.val

/-- The expected total revenue of a 2-bidder mechanism `M` when joint
    valuations are drawn from `prior` and `M` produces outcome
    distributions. -/
def expectedRevenue (n : Nat)
    (M : StochasticMatrix (n * n) ((2 * n) * (2 * n)))
    (prior : Fin (n * n) → Rat) : Rat :=
  Fin.sumRat (fun v : Fin (n * n) =>
    prior v
    * Fin.sumRat (fun o : Fin ((2 * n) * (2 * n)) =>
        M.entry v o * (outcomeRevenue n o : Nat).cast))

/-! ## Pointwise revenue comparison

  For truthful bidding (joint bid = joint valuation), first-price
  extracts the highest bid as revenue, while second-price extracts
  the lowest.  Hence at every outcome, the first-price revenue is
  weakly greater than the second-price revenue. -/

/-- Pointwise revenue comparison: first-price ≥ second-price at every
    joint-bid input.  Specialised to the truthful case via the
    auction assembly (truthful bidders submit valuations as bids). -/
theorem fpsb_revenue_ge_spsb (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbFn n i) ≥ outcomeRevenue n (spsbFn n i) := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue fpsbFn spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : i.val / n ≤ i.val % n
  · simp [hb]
  · simp [hb]; omega

/-- Closed-form fpsb revenue: at every joint bid `i`, the first-price
    revenue equals the maximum of the two bids.  This is the
    winner-pays-own-bid rule expressed as a `max` selector. -/
theorem fpsb_revenue_eq_max (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbFn n i)
    = max (Fin.first i).val (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue fpsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : (Fin.first i).val ≥ (Fin.second i).val
  · simp [hb]; omega
  · simp [hb]; omega

/-- Closed-form spsb revenue: at every joint bid `i`, the second-price
    (Vickrey) revenue equals the minimum of the two bids.  This is
    the winner-pays-others-bid rule expressed as a `min` selector. -/
theorem spsb_revenue_eq_min (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (spsbFn n i)
    = min (Fin.first i).val (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : (Fin.first i).val ≥ (Fin.second i).val
  · simp [hb]; omega
  · simp [hb]; omega

/-- Pointwise revenue gap: `fpsb - spsb = |b1 - b2|` as Nat.  Combines
    the `max`/`min` closed forms to give the discrete IPV revenue
    gap between the two formats at every joint bid. -/
theorem fpsb_minus_spsb_revenue (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbFn n i)
    = outcomeRevenue n (spsbFn n i)
      + (max (Fin.first i).val (Fin.second i).val
        - min (Fin.first i).val (Fin.second i).val) := by
  rw [fpsb_revenue_eq_max, spsb_revenue_eq_min]
  omega

/-! ## Revenue equivalence as a relation

  The canonical statement of Myerson's Revenue Equivalence Theorem
  (RET) is that, in the IPV setting with risk-neutral bidders playing
  symmetric Bayes-Nash equilibrium, all auction formats that
  allocate to the highest-valuation bidder and give zero expected
  surplus to the lowest type yield the same expected revenue.

  We record the relation `IsRevenueEquivalent` here as a `Prop`
  comparing two mechanisms' expected revenues under a common prior,
  and prove it is an equivalence relation.  The canonical RET — that
  fpsb under equilibrium shading and spsb under truthful bidding are
  related by this relation for any symmetric IPV prior — is left as a
  named target for the future once the envelope-theorem layer
  arrives. -/

/-- Two mechanisms are *revenue equivalent under `prior`* iff their
    expected revenues agree.

    This is a pointwise statement at the level of expected revenues;
    the canonical RET ties this to equilibrium-strategy-adjusted
    versions of the four standard auction formats. -/
def IsRevenueEquivalent (n : Nat)
    (M1 M2 : StochasticMatrix (n * n) ((2 * n) * (2 * n)))
    (prior : Fin (n * n) → Rat) : Prop :=
  expectedRevenue n M1 prior = expectedRevenue n M2 prior

/-- Reflexivity: every mechanism is revenue equivalent to itself. -/
theorem IsRevenueEquivalent.refl' {n : Nat}
    (M : StochasticMatrix (n * n) ((2 * n) * (2 * n)))
    (prior : Fin (n * n) → Rat) :
    IsRevenueEquivalent n M M prior :=
  Eq.refl _

/-- Symmetry of the relation. -/
theorem IsRevenueEquivalent.symm' {n : Nat}
    {M1 M2 : StochasticMatrix (n * n) ((2 * n) * (2 * n))}
    {prior : Fin (n * n) → Rat}
    (h : IsRevenueEquivalent n M1 M2 prior) :
    IsRevenueEquivalent n M2 M1 prior :=
  h.symm

/-- Transitivity of the relation. -/
theorem IsRevenueEquivalent.trans' {n : Nat}
    {M1 M2 M3 : StochasticMatrix (n * n) ((2 * n) * (2 * n))}
    {prior : Fin (n * n) → Rat}
    (h12 : IsRevenueEquivalent n M1 M2 prior)
    (h23 : IsRevenueEquivalent n M2 M3 prior) :
    IsRevenueEquivalent n M1 M3 prior :=
  h12.trans h23

/-- The uniform prior over joint valuations `Fin (n * n)`. -/
def uniformPrior (n : Nat) : Fin (n * n) → Rat :=
  fun _ => 1 / ((n * n : Nat) : Rat)

/-! ## Strategic-equivalence revenue corollaries

  English ≅ SecondPriceSealedBid and Dutch ≅ FirstPriceSealedBid at
  the mechanism level (kernel rfl), so their expected revenues match
  trivially under any prior.  These are the kernel-level Revenue
  Equivalence statements between {English, SPSB} and {Dutch, FPSB}. -/

/-- English auction has the same expected revenue as Vickrey under
    any prior — corollary of `english_eq_secondPrice`. -/
theorem english_revenue_eq_spsb (n : Nat) (prior : Fin (n * n) → Rat) :
    expectedRevenue n (englishAuction n) prior
    = expectedRevenue n (secondPriceSealedBid n) prior := rfl

/-- Dutch auction has the same expected revenue as first-price
    sealed-bid under any prior — corollary of `dutch_eq_firstPrice`. -/
theorem dutch_revenue_eq_fpsb (n : Nat) (prior : Fin (n * n) → Rat) :
    expectedRevenue n (dutchAuction n) prior
    = expectedRevenue n (firstPriceSealedBid n) prior := rfl

/-- English ≅ SPSB revenue equivalence as an inhabitant of the
    `IsRevenueEquivalent` relation. -/
theorem english_is_revenue_equivalent_spsb (n : Nat)
    (prior : Fin (n * n) → Rat) :
    IsRevenueEquivalent n (englishAuction n) (secondPriceSealedBid n) prior :=
  rfl

/-- Dutch ≅ FPSB revenue equivalence as an inhabitant of the
    `IsRevenueEquivalent` relation. -/
theorem dutch_is_revenue_equivalent_fpsb (n : Nat)
    (prior : Fin (n * n) → Rat) :
    IsRevenueEquivalent n (dutchAuction n) (firstPriceSealedBid n) prior :=
  rfl

end AuctionCat
