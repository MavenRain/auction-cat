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

/-- **Revenue symmetry under bidder swap**: swapping bidder 1 and
    bidder 2's outcomes preserves the total revenue, since revenue is
    the sum of both bidders' prices. -/
theorem outcomeRevenue_swap_symmetric (n : Nat)
    (i : Fin ((2 * n) * (2 * n))) (h_pos : 0 < 2 * n) :
    outcomeRevenue n i
    = outcomeRevenue n (Fin.pair (Fin.second i) (Fin.first i)) := by
  unfold outcomeRevenue
  simp only [Fin.first_pair, Fin.second_pair h_pos]
  omega

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
  by_cases hb : i.val / n ≤ i.val % n
  · simp [hb]
  · simp [hb]; omega

/-- Closed-form spsb revenue: at every joint bid `i`, the second-price
    (Vickrey) revenue equals the minimum of the two bids.  This is
    the winner-pays-others-bid rule expressed as a `min` selector. -/
theorem spsb_revenue_eq_min (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (spsbFn n i)
    = min (Fin.first i).val (Fin.second i).val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue spsbFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hb : i.val / n ≤ i.val % n
  · simp [hb]
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

/-- **Pointwise Dutch ≥ English revenue** under truthful play.
    Combines the strategic-equivalence rfls (Dutch = FPSB, English =
    SPSB at the kernel level) with the pointwise FPSB ≥ SPSB revenue
    dominance.  Dutch extracts max bid, English extracts min bid, so
    Dutch ≥ English pointwise. -/
theorem dutch_revenue_ge_english (n : Nat) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbFn n i) ≥ outcomeRevenue n (spsbFn n i) :=
  fpsb_revenue_ge_spsb n i

/-! ## Reserve-price revenue closed forms

  The two-bidder formats with a reserve price `r` (`fpsbReserveFn`,
  `spsbReserveFn`) extend the `max`/`min` revenue closed forms with a
  *no-sale* region: when both bids fall below `r` the item is withheld
  and revenue is `0`.  Above the reserve the winner is the high bidder,
  so first-price revenue is still the top bid, while second-price
  revenue is `max(r, low bid)` — the reserve lifts the winner's payment
  from the loser's bid up to `r`.  These restore the reserve revenue
  layer to parity with the no-reserve `fpsb_revenue_eq_max` /
  `spsb_revenue_eq_min` / `fpsb_revenue_ge_spsb` trio. -/

/-- **Closed-form fpsb-with-reserve revenue.**  At joint bid `i` with
    reserve `r`, first-price revenue is the higher bid when it clears
    the reserve, and `0` otherwise (the item goes unsold). -/
theorem fpsbReserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r i)
    = if r.val ≤ max (Fin.first i).val (Fin.second i).val
      then max (Fin.first i).val (Fin.second i).val else 0 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue fpsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val, apply_ite Fin.val, ge_iff_le]
  (repeat' split) <;> omega

/-- **Closed-form spsb-with-reserve revenue.**  At joint bid `i` with
    reserve `r`, second-price revenue is `max(r, low bid)` when the high
    bid clears the reserve, and `0` otherwise.  The reserve raises the
    winner's payment from the losing bid up to the reserve floor. -/
theorem spsbReserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (spsbReserveFn n r i)
    = if r.val ≤ max (Fin.first i).val (Fin.second i).val
      then max r.val (min (Fin.first i).val (Fin.second i).val) else 0 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold outcomeRevenue spsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val, apply_ite Fin.val, ge_iff_le]
  (repeat' split) <;> omega

/-- **Reserve revenue dominance.**  First-price-with-reserve weakly
    dominates second-price-with-reserve in revenue at every joint bid:
    above the reserve the gap is `max - max(r, min)`, and below it both
    raise `0`.  Reserve analogue of `fpsb_revenue_ge_spsb`. -/
theorem fpsbReserve_revenue_ge_spsbReserve (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r i) ≥ outcomeRevenue n (spsbReserveFn n r i) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq]
  (repeat' split) <;> omega

/-- **The reserve guarantee.**  Whenever a sale occurs — the high bid
    clears the reserve — the second-price-with-reserve format pays the
    seller at least the reserve `r`.  This is the defining purpose of a
    reserve price: a floor on any completed sale. -/
theorem spsbReserve_revenue_ge_reserve_of_sale (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : r.val ≤ max (Fin.first i).val (Fin.second i).val) :
    outcomeRevenue n (spsbReserveFn n r i) ≥ r.val := by
  rw [spsbReserve_revenue_eq, if_pos h]
  omega

/-- **No sale below the reserve.**  When both bids fall strictly below
    the reserve `r`, the first-price-with-reserve format withholds the
    item and raises `0` revenue. -/
theorem fpsbReserve_revenue_eq_zero_of_below_reserve (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : max (Fin.first i).val (Fin.second i).val < r.val) :
    outcomeRevenue n (fpsbReserveFn n r i) = 0 := by
  rw [fpsbReserve_revenue_eq, if_neg (by omega)]

/-- **The reserve guarantee, first-price side.**  Whenever a sale occurs
    (the high bid clears the reserve), the first-price-with-reserve format
    also pays the seller at least the reserve `r`.  The winner pays the
    full top bid, and that bid clears `r`, so the floor is immediate.
    First-price twin of `spsbReserve_revenue_ge_reserve_of_sale`. -/
theorem fpsbReserve_revenue_ge_reserve_of_sale (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : r.val ≤ max (Fin.first i).val (Fin.second i).val) :
    outcomeRevenue n (fpsbReserveFn n r i) ≥ r.val := by
  rw [fpsbReserve_revenue_eq, if_pos h]
  omega

/-- **No sale below the reserve, second-price side.**  When both bids fall
    strictly below the reserve `r`, the second-price-with-reserve format
    withholds the item and raises `0` revenue.  Second-price twin of
    `fpsbReserve_revenue_eq_zero_of_below_reserve`. -/
theorem spsbReserve_revenue_eq_zero_of_below_reserve (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : max (Fin.first i).val (Fin.second i).val < r.val) :
    outcomeRevenue n (spsbReserveFn n r i) = 0 := by
  rw [spsbReserve_revenue_eq, if_neg (by omega)]

/-- **Strict reserve revenue dominance.**  When the two bids differ and the
    high bid strictly exceeds the reserve, first-price-with-reserve extracts
    strictly more revenue than second-price-with-reserve: the gap is
    `max - max(r, min) > 0`.  Reserve analogue of `fpsb_revenue_gt_spsb_of_ne`,
    strengthening the weak dominance `fpsbReserve_revenue_ge_spsbReserve`. -/
theorem fpsbReserve_revenue_gt_spsbReserve_of_ne (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h_ne : (Fin.first i).val ≠ (Fin.second i).val)
    (h_r : r.val < max (Fin.first i).val (Fin.second i).val) :
    outcomeRevenue n (fpsbReserveFn n r i) > outcomeRevenue n (spsbReserveFn n r i) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq, if_pos (by omega), if_pos (by omega)]
  omega

/-- **Pointwise reserve revenue gap.**  First-price-with-reserve revenue
    equals second-price-with-reserve revenue plus the surplus the reserve
    format leaves above its floor: `max - max(r, min)` when a sale occurs,
    and `0` in the no-sale region where both formats withhold the item.
    Reserve analogue of `fpsb_minus_spsb_revenue`. -/
theorem fpsbReserve_minus_spsbReserve_revenue (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r i)
    = outcomeRevenue n (spsbReserveFn n r i)
      + (if r.val ≤ max (Fin.first i).val (Fin.second i).val
        then max (Fin.first i).val (Fin.second i).val
          - max r.val (min (Fin.first i).val (Fin.second i).val)
        else 0) := by
  rw [fpsbReserve_revenue_eq, spsbReserve_revenue_eq]
  (repeat' split) <;> omega

/-- **Bidder-anonymity of fpsb-with-reserve revenue.**  Swapping the two
    bidders' bids leaves first-price-with-reserve revenue unchanged: the
    format prices off `max` of the bids, symmetric in the bidders.  This is
    the bid-input analogue of `outcomeRevenue_swap_symmetric` (which swaps
    the outcome components) specialised to the reserve mechanism. -/
theorem fpsbReserve_revenue_bid_swap (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (fpsbReserveFn n r (Fin.pair (Fin.second i) (Fin.first i)))
    = outcomeRevenue n (fpsbReserveFn n r i) := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  rw [fpsbReserve_revenue_eq, fpsbReserve_revenue_eq,
      Fin.first_pair, Fin.second_pair hn]
  (repeat' split) <;> omega

/-- **Bidder-anonymity of spsb-with-reserve revenue.**  Swapping the two
    bidders' bids leaves second-price-with-reserve revenue unchanged; the
    winner still pays `max(r, low bid)` whenever the high bid clears the
    reserve.  Reserve second-price twin of `fpsbReserve_revenue_bid_swap`. -/
theorem spsbReserve_revenue_bid_swap (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    outcomeRevenue n (spsbReserveFn n r (Fin.pair (Fin.second i) (Fin.first i)))
    = outcomeRevenue n (spsbReserveFn n r i) := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  rw [spsbReserve_revenue_eq, spsbReserve_revenue_eq,
      Fin.first_pair, Fin.second_pair hn]
  (repeat' split) <;> omega

/-! ## Bundled reserve-revenue summaries -/

/-- **Main reserve-price revenue results.**  The unconditional core of the
    two-bidder reserve-revenue layer, bundled into one citable node: both
    closed forms (first-price = the top bid when it clears `r`, else `0`;
    second-price = `max(r, low bid)` on a sale, else `0`), the pointwise
    weak revenue dominance `fpsbReserve ≥ spsbReserve`, the exact revenue
    gap between the two formats, and the bidder-anonymity (bid-swap
    invariance) of each.  Reserve analogue of the no-reserve
    `fpsb`/`spsb` revenue results.  The strict dominance
    `fpsbReserve_revenue_gt_spsbReserve_of_ne` is a separate node: it needs
    the extra distinct-bids and strict-clearance hypotheses, so it is
    intentionally not bundled here. -/
theorem reserveRevenue_main (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    -- closed forms
    outcomeRevenue n (fpsbReserveFn n r i)
      = (if r.val ≤ max (Fin.first i).val (Fin.second i).val
         then max (Fin.first i).val (Fin.second i).val else 0)
    ∧ outcomeRevenue n (spsbReserveFn n r i)
      = (if r.val ≤ max (Fin.first i).val (Fin.second i).val
         then max r.val (min (Fin.first i).val (Fin.second i).val) else 0)
    -- weak revenue dominance
    ∧ outcomeRevenue n (fpsbReserveFn n r i) ≥ outcomeRevenue n (spsbReserveFn n r i)
    -- exact revenue gap
    ∧ outcomeRevenue n (fpsbReserveFn n r i)
      = outcomeRevenue n (spsbReserveFn n r i)
        + (if r.val ≤ max (Fin.first i).val (Fin.second i).val
          then max (Fin.first i).val (Fin.second i).val
            - max r.val (min (Fin.first i).val (Fin.second i).val)
          else 0)
    -- bidder anonymity of each format
    ∧ outcomeRevenue n (fpsbReserveFn n r (Fin.pair (Fin.second i) (Fin.first i)))
      = outcomeRevenue n (fpsbReserveFn n r i)
    ∧ outcomeRevenue n (spsbReserveFn n r (Fin.pair (Fin.second i) (Fin.first i)))
      = outcomeRevenue n (spsbReserveFn n r i) :=
  ⟨fpsbReserve_revenue_eq n r i,
   spsbReserve_revenue_eq n r i,
   fpsbReserve_revenue_ge_spsbReserve n r i,
   fpsbReserve_minus_spsbReserve_revenue n r i,
   fpsbReserve_revenue_bid_swap n r i,
   spsbReserve_revenue_bid_swap n r i⟩

/-- **The reserve guarantee, both formats.**  Whenever a sale occurs (the
    high bid clears the reserve `r`), both the first-price and second-price
    reserve formats pay the seller at least the reserve.  This is the
    defining purpose of a reserve price: a floor on every completed sale,
    in either format.  Bundles `fpsbReserve_revenue_ge_reserve_of_sale`
    and `spsbReserve_revenue_ge_reserve_of_sale`. -/
theorem reserveRevenue_ge_reserve_of_sale_main (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : r.val ≤ max (Fin.first i).val (Fin.second i).val) :
    outcomeRevenue n (fpsbReserveFn n r i) ≥ r.val
    ∧ outcomeRevenue n (spsbReserveFn n r i) ≥ r.val :=
  ⟨fpsbReserve_revenue_ge_reserve_of_sale n r i h,
   spsbReserve_revenue_ge_reserve_of_sale n r i h⟩

/-- **No sale below the reserve, both formats.**  When both bids fall
    strictly below the reserve `r`, neither reserve format sells: the
    first-price and second-price formats alike withhold the item and raise
    `0` revenue.  Bundles `fpsbReserve_revenue_eq_zero_of_below_reserve`
    and `spsbReserve_revenue_eq_zero_of_below_reserve`. -/
theorem reserveRevenue_eq_zero_of_below_reserve_main (n : Nat) (r : Fin n) (i : Fin (n * n))
    (h : max (Fin.first i).val (Fin.second i).val < r.val) :
    outcomeRevenue n (fpsbReserveFn n r i) = 0
    ∧ outcomeRevenue n (spsbReserveFn n r i) = 0 :=
  ⟨fpsbReserve_revenue_eq_zero_of_below_reserve n r i h,
   spsbReserve_revenue_eq_zero_of_below_reserve n r i h⟩

end AuctionCat
