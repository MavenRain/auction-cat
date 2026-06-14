import AuctionCat.FirstPrice
import AuctionCat.SecondPrice
import AuctionCat.English
import AuctionCat.Dutch
import AuctionCat.Reserve

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

/-- **fpsb and spsb have IDENTICAL allocation rules**: bidder 1
    gets the item in fpsb iff bidder 1 gets the item in spsb (both
    formats use `b1 ≥ b2 → bidder 1 wins`).  The two formats differ
    only in PRICING, not allocation. -/
theorem fpsb_spsb_same_allocation (n : Nat) (i : Fin (n * n)) :
    (Fin.first (Fin.first (fpsbFn n i))).val
    = (Fin.first (Fin.first (spsbFn n i))).val := by
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
  · rw [(fpsb_bidder1_allocated_iff_higher_bid n i).mpr h,
        (spsb_bidder1_allocated_iff_higher_bid n i).mpr h]
  · have h_fpsb : (Fin.first (Fin.first (fpsbFn n i))).val ≠ 1 := by
      intro hcontra
      exact h ((fpsb_bidder1_allocated_iff_higher_bid n i).mp hcontra)
    have h_spsb : (Fin.first (Fin.first (spsbFn n i))).val ≠ 1 := by
      intro hcontra
      exact h ((spsb_bidder1_allocated_iff_higher_bid n i).mp hcontra)
    have hb1 := (Fin.first (Fin.first (fpsbFn n i))).isLt
    have hb2 := (Fin.first (Fin.first (spsbFn n i))).isLt
    omega

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

/-- Strict pointwise dominance: when the two bids differ, fpsb
    extracts strictly more revenue than spsb (the gap is exactly
    `|b1 - b2| > 0`). -/
theorem fpsb_revenue_gt_spsb_of_ne (n : Nat) (i : Fin (n * n))
    (h_ne : (Fin.first i).val ≠ (Fin.second i).val) :
    outcomeRevenue n (fpsbFn n i) > outcomeRevenue n (spsbFn n i) := by
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

/-! ## Reserve-auction closed-form revenue

  Reserve auctions have two regimes per joint bid: if the highest
  bid clears the reserve, the auction allocates and extracts revenue
  per the underlying format; otherwise no one wins and revenue = 0. -/

/-- Closed-form fpsbReserve revenue: if `max(b1, b2) ≥ r`, the
    revenue equals `max(b1, b2)` (winner pays own bid); else 0. -/
theorem fpsbReserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r i)
    = (if max (Fin.first i).val (Fin.second i).val ≥ r.val
        then max (Fin.first i).val (Fin.second i).val
        else 0) := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue fpsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : (Fin.first i).val ≥ (Fin.second i).val
  · by_cases hr1 : (Fin.first i).val ≥ r.val
    · simp [hb, hr1]; omega
    · simp [hb, hr1]; omega
  · by_cases hr2 : (Fin.second i).val ≥ r.val
    · simp [hb, hr2]; omega
    · simp [hb, hr2]; omega

/-- Closed-form spsbReserve revenue: if `max(b1, b2) ≥ r`, the
    revenue equals `max(r, min(b1, b2))` (winner pays max of reserve
    and loser's bid); else 0. -/
theorem spsbReserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (spsbReserveFn n r i)
    = (if max (Fin.first i).val (Fin.second i).val ≥ r.val
        then max r.val (min (Fin.first i).val (Fin.second i).val)
        else 0) := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue spsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : (Fin.first i).val ≥ (Fin.second i).val
  · by_cases hr1 : (Fin.first i).val ≥ r.val
    · simp [hb, hr1]; omega
    · simp [hb, hr1]; omega
  · by_cases hr2 : (Fin.second i).val ≥ r.val
    · simp [hb, hr2]; omega
    · simp [hb, hr2]; omega

/-- Pointwise revenue comparison for reserve auctions: fpsbReserve ≥
    spsbReserve at every joint-bid input.  In the no-allocation
    regime both are 0; in the allocation regime fpsb extracts
    `max(b1,b2)` while spsb extracts `max(r, min(b1,b2))`, and
    `max(b1,b2) ≥ max(r, min(b1,b2))` whenever the auction allocates. -/
theorem fpsbReserve_revenue_ge_spsbReserve (n : Nat) (r : Fin n)
    (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r i)
    ≥ outcomeRevenue n (spsbReserveFn n r i) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq]
  by_cases hr : max (Fin.first i).val (Fin.second i).val ≥ r.val
  · simp [hr]; omega
  · simp [hr]

/-! ## Trivial reserve = no reserve

  At `r = 0` the reserve is non-binding (every bid clears 0), so
  reserve auctions reduce to their no-reserve counterparts at the
  revenue level. -/

/-- At reserve `r = 0`, fpsbReserve revenue equals fpsb revenue at
    every joint-bid input. -/
theorem fpsbReserve_zero_revenue_eq_fpsb (n : Nat) (hn : 0 < n)
    (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n ⟨0, hn⟩ i)
    = outcomeRevenue n (fpsbFn n i) := by
  rw [fpsbReserve_revenue_eq, fpsb_revenue_eq_max]
  simp

/-- At reserve `r = 0`, spsbReserve revenue equals spsb revenue at
    every joint-bid input.  Note: `max 0 (min b1 b2) = min b1 b2`
    so the reserve drops out. -/
theorem spsbReserve_zero_revenue_eq_spsb (n : Nat) (hn : 0 < n)
    (i : Fin (n * n)) :
    outcomeRevenue n (spsbReserveFn n ⟨0, hn⟩ i)
    = outcomeRevenue n (spsbFn n i) := by
  rw [spsbReserve_revenue_eq, spsb_revenue_eq_min]
  simp

/-! ## Maximal-reserve revenue collapse

  At `r = n - 1` (the highest possible bid in `Fin n`), the
  allocation condition `max ≥ r` forces `max = n - 1`, so both
  fpsbReserve and spsbReserve extract exactly `n - 1` per
  allocation.  The two formats coincide pointwise at this reserve. -/

/-- At maximal reserve `r = n - 1`, fpsbReserve and spsbReserve give
    identical revenue at every joint-bid input.  Reason: the allocation
    condition `max ≥ n - 1` forces `max = n - 1` (since bids live in
    `Fin n`), so the winner pays exactly `r`. -/
theorem fpsbReserve_max_revenue_eq_spsbReserve_max (n : Nat) (hn : 0 < n)
    (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n ⟨n - 1, by omega⟩ i)
    = outcomeRevenue n (spsbReserveFn n ⟨n - 1, by omega⟩ i) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq]
  have hb1 := (Fin.first i).isLt
  have hb2 := (Fin.second i).isLt
  by_cases hr : max (Fin.first i).val (Fin.second i).val ≥ n - 1
  · simp [hr]; omega
  · simp [hr]

/-- Strict pointwise dominance for reserve auctions: when the
    auction allocates (max ≥ r), the top bidder strictly clears the
    reserve (max > r), AND bids differ, fpsbReserve extracts
    strictly more than spsbReserve.  The two strict conditions
    together ensure the spsbReserve payment `max(r, min)` is
    strictly below `max`. -/
theorem fpsbReserve_revenue_gt_spsbReserve_of_strict (n : Nat) (r : Fin n)
    (i : Fin (n * n))
    (h_strict : max (Fin.first i).val (Fin.second i).val > r.val)
    (h_ne : (Fin.first i).val ≠ (Fin.second i).val) :
    outcomeRevenue n (fpsbReserveFn n r i)
    > outcomeRevenue n (spsbReserveFn n r i) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq]
  have hr : max (Fin.first i).val (Fin.second i).val ≥ r.val := by omega
  simp [hr]
  omega

end AuctionCat
