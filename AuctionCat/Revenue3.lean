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

/-! ## Reserve prices strictly raise Vickrey revenue (3 bidders)

  A binding reserve at `r = 1` over binary valuations `Fin 2` turns the
  three-bidder second-price mechanism from "always sell to the winner
  at the second-highest bid" into "sell only if some bid clears the
  reserve, at price `max r (second-highest bid)`".  Under the uniform
  prior this raises the seller's expected revenue from `1 / 2` (spsb3:
  the item always sells and is priced at the second-highest bid, which
  is `1` only when at least two bidders value it at `1`) to `7 / 8`
  (spsb3Reserve: the item sells whenever any bidder values it at `1`
  and is then always priced at the reserve).  This is the central point
  of a reserve price: here it strictly dominates the no-reserve Vickrey
  auction in expectation. -/

/-- Three-bidder Vickrey with a binding reserve `r = 1`, `X = 2`,
    uniform prior, truthful bidding: expected revenue = 7/8. -/
theorem spsb3Reserve_revenue_eq_uniform :
    expectedRevenue3 2 (spsb3Reserve 2 (⟨1, by decide⟩ : Fin 2))
      (uniformPrior3 2) = 7 / 8 := by
  unfold expectedRevenue3 uniformPrior3
  native_decide

/-- A binding reserve strictly raises three-bidder Vickrey expected
    revenue over the no-reserve auction (`7 / 8 > 1 / 2`) at `X = 2`
    under the uniform prior with truthful bidding. -/
theorem spsb3Reserve_revenue_gt_spsb3_uniform :
    expectedRevenue3 2 (spsb3Reserve 2 (⟨1, by decide⟩ : Fin 2))
      (uniformPrior3 2)
    > expectedRevenue3 2 (secondPriceSealedBid3 2) (uniformPrior3 2) := by
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

/-! ## Reserve-price revenue closed forms (three bidders)

  Closed forms for the two three-bidder reserve mechanisms.  Writing `M`
  for the highest of the three bids, a sale occurs exactly when `M` clears
  the reserve `r`.  On a sale the first-price format collects the winning
  (highest) bid `M`, while the second-price format collects `max r s`,
  where `s` is the second-highest bid; below the reserve both formats
  withhold the item and raise `0`.  Three-bidder analogues of the
  two-bidder `fpsbReserve_revenue_eq` / `spsbReserve_revenue_eq`. -/

/-- **Closed-form three-bidder fpsb-with-reserve revenue.**  First-price
    revenue is the highest of the three bids when it clears the reserve
    `r`, and `0` otherwise (the item goes unsold). -/
theorem fpsb3Reserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i)
    = if r.val ≤ max (Fin.first (Fin.first i)).val
                     (max (Fin.second (Fin.first i)).val (Fin.second i).val)
      then max (Fin.first (Fin.first i)).val
               (max (Fin.second (Fin.first i)).val (Fin.second i).val)
      else 0 := by
  have hn   : 0 < n :=
    Nat.pos_of_mul_pos_left (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have h2   : 0 < 2 := by decide
  have h2n  : 0 < 2 * n := by omega
  have h2n2 : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  unfold outcomeRevenue3 fpsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n2, Fin.second_pair h2n,
             Fin.second_pair h2, Fin.first_val, Fin.second_val,
             apply_ite Fin.val, ge_iff_le]
  (repeat' split) <;> omega

/-- **Closed-form three-bidder spsb-with-reserve revenue.**  Second-price
    revenue is `max r s` (the reserve floor or the second-highest bid `s`,
    whichever is larger) when the highest bid clears the reserve, and `0`
    otherwise.  The second-highest of three bids is the largest of their
    three pairwise minima. -/
theorem spsb3Reserve_revenue_eq (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    outcomeRevenue3 n (spsb3ReserveFn n r i)
    = if r.val ≤ max (Fin.first (Fin.first i)).val
                     (max (Fin.second (Fin.first i)).val (Fin.second i).val)
      then max r.val
               (max (min (Fin.first (Fin.first i)).val (Fin.second (Fin.first i)).val)
                    (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
                         (min (Fin.second (Fin.first i)).val (Fin.second i).val)))
      else 0 := by
  have hn   : 0 < n :=
    Nat.pos_of_mul_pos_left (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have h2   : 0 < 2 := by decide
  have h2n  : 0 < 2 * n := by omega
  have h2n2 : 0 < (2 * n) * (2 * n) := Nat.mul_pos h2n h2n
  unfold outcomeRevenue3 spsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n2, Fin.second_pair h2n,
             Fin.second_pair h2, Fin.first_val, Fin.second_val,
             apply_ite Fin.val, ge_iff_le]
  (repeat' split) <;> omega

/-- **Three-bidder reserve revenue dominance.**  First-price-with-reserve
    weakly dominates second-price-with-reserve in revenue at every joint
    bid and reserve: above the reserve the first-price winner pays the full
    top bid, while the second-price winner pays only `max r s` (the reserve
    or the second-highest bid); below the reserve both raise `0`.
    Three-bidder analogue of `fpsbReserve_revenue_ge_spsbReserve`. -/
theorem fpsb3Reserve_revenue_ge_spsb3Reserve (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i) ≥ outcomeRevenue3 n (spsb3ReserveFn n r i) := by
  rw [fpsb3Reserve_revenue_eq, spsb3Reserve_revenue_eq]
  (repeat' split) <;> omega

/-- **The reserve guarantee (three bidders).**  Whenever a sale occurs (the
    highest of the three bids clears the reserve), the three-bidder
    second-price-with-reserve format pays the seller at least the reserve
    `r`: a floor on any completed sale.  Three-bidder analogue of
    `spsbReserve_revenue_ge_reserve_of_sale`. -/
theorem spsb3Reserve_revenue_ge_reserve_of_sale (n : Nat) (r : Fin n) (i : Fin ((n * n) * n))
    (h : r.val ≤ max (Fin.first (Fin.first i)).val
                     (max (Fin.second (Fin.first i)).val (Fin.second i).val)) :
    outcomeRevenue3 n (spsb3ReserveFn n r i) ≥ r.val := by
  rw [spsb3Reserve_revenue_eq, if_pos h]
  omega

/-- **The reserve guarantee, first-price side (three bidders).**  Whenever a
    sale occurs (the highest bid clears the reserve), the three-bidder
    first-price-with-reserve format also pays the seller at least the
    reserve `r`: the winner pays the full top bid, which clears `r`.
    First-price twin of `spsb3Reserve_revenue_ge_reserve_of_sale`. -/
theorem fpsb3Reserve_revenue_ge_reserve_of_sale (n : Nat) (r : Fin n) (i : Fin ((n * n) * n))
    (h : r.val ≤ max (Fin.first (Fin.first i)).val
                     (max (Fin.second (Fin.first i)).val (Fin.second i).val)) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i) ≥ r.val := by
  rw [fpsb3Reserve_revenue_eq, if_pos h]
  omega

/-- **No sale below the reserve (three bidders).**  When all three bids fall
    strictly below the reserve `r`, the first-price-with-reserve format
    withholds the item and raises `0` revenue.  Three-bidder analogue of
    `fpsbReserve_revenue_eq_zero_of_below_reserve`. -/
theorem fpsb3Reserve_revenue_eq_zero_of_below_reserve (n : Nat) (r : Fin n) (i : Fin ((n * n) * n))
    (h : max (Fin.first (Fin.first i)).val
             (max (Fin.second (Fin.first i)).val (Fin.second i).val) < r.val) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i) = 0 := by
  rw [fpsb3Reserve_revenue_eq, if_neg (by omega)]

/-- **No sale below the reserve, second-price side (three bidders).**  When
    all three bids fall strictly below the reserve `r`, the
    second-price-with-reserve format withholds the item and raises `0`
    revenue.  Second-price twin of
    `fpsb3Reserve_revenue_eq_zero_of_below_reserve`. -/
theorem spsb3Reserve_revenue_eq_zero_of_below_reserve (n : Nat) (r : Fin n) (i : Fin ((n * n) * n))
    (h : max (Fin.first (Fin.first i)).val
             (max (Fin.second (Fin.first i)).val (Fin.second i).val) < r.val) :
    outcomeRevenue3 n (spsb3ReserveFn n r i) = 0 := by
  rw [spsb3Reserve_revenue_eq, if_neg (by omega)]

/-- **Strict reserve revenue dominance (three bidders).**  When the highest
    bid is unique (the second-highest bid falls strictly below it) and the
    reserve `r` sits strictly below the top bid, first-price-with-reserve
    extracts strictly more revenue than second-price-with-reserve: the top
    bidder pays their full winning bid rather than `max r s`.  Three-bidder
    analogue of `fpsbReserve_revenue_gt_spsbReserve_of_ne`, strengthening
    the weak dominance `fpsb3Reserve_revenue_ge_spsb3Reserve`. -/
theorem fpsb3Reserve_revenue_gt_spsb3Reserve_of_unique_top (n : Nat) (r : Fin n) (i : Fin ((n * n) * n))
    (h_top : max (min (Fin.first (Fin.first i)).val (Fin.second (Fin.first i)).val)
                 (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
                      (min (Fin.second (Fin.first i)).val (Fin.second i).val))
             < max (Fin.first (Fin.first i)).val
                   (max (Fin.second (Fin.first i)).val (Fin.second i).val))
    (h_r : r.val < max (Fin.first (Fin.first i)).val
                       (max (Fin.second (Fin.first i)).val (Fin.second i).val)) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i) > outcomeRevenue3 n (spsb3ReserveFn n r i) := by
  rw [fpsb3Reserve_revenue_eq, spsb3Reserve_revenue_eq, if_pos (by omega), if_pos (by omega)]
  omega

/-- **Pointwise reserve revenue gap (three bidders).**  First-price-with-
    reserve revenue equals second-price-with-reserve revenue plus the
    surplus the reserve format leaves above its floor: `M - max r s` (top
    bid minus the second-price price) when a sale occurs, and `0` in the
    no-sale region where both formats withhold the item.  Three-bidder
    analogue of `fpsbReserve_minus_spsbReserve_revenue`. -/
theorem fpsb3Reserve_minus_spsb3Reserve_revenue (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    outcomeRevenue3 n (fpsb3ReserveFn n r i)
    = outcomeRevenue3 n (spsb3ReserveFn n r i)
      + (if r.val ≤ max (Fin.first (Fin.first i)).val
                        (max (Fin.second (Fin.first i)).val (Fin.second i).val)
        then max (Fin.first (Fin.first i)).val
                 (max (Fin.second (Fin.first i)).val (Fin.second i).val)
          - max r.val
                (max (min (Fin.first (Fin.first i)).val (Fin.second (Fin.first i)).val)
                     (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
                          (min (Fin.second (Fin.first i)).val (Fin.second i).val)))
        else 0) := by
  rw [fpsb3Reserve_revenue_eq, spsb3Reserve_revenue_eq]
  (repeat' split) <;> omega

/-- **Main three-bidder reserve-price revenue results.**  The unconditional
    core of the three-bidder reserve-revenue layer, bundled into one citable
    node: both closed forms (first-price = the top of the three bids when it
    clears `r`, else `0`; second-price = `max r s` on a sale, else `0`), the
    pointwise weak revenue dominance `fpsb3Reserve ≥ spsb3Reserve`, and the
    exact revenue gap between the two formats.  Three-bidder analogue of the
    unconditional core of `reserveRevenue_main` (the two-bidder bundle also
    carries bidder-anonymity conjuncts with no three-bidder counterpart yet).
    The strict dominance
    `fpsb3Reserve_revenue_gt_spsb3Reserve_of_unique_top` is a separate node: it needs
    the extra unique-top and strict-clearance hypotheses, so it is
    intentionally not bundled here. -/
theorem reserveRevenue3_main (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    -- closed forms
    outcomeRevenue3 n (fpsb3ReserveFn n r i)
      = (if r.val ≤ max (Fin.first (Fin.first i)).val
                        (max (Fin.second (Fin.first i)).val (Fin.second i).val)
         then max (Fin.first (Fin.first i)).val
                  (max (Fin.second (Fin.first i)).val (Fin.second i).val)
         else 0)
    ∧ outcomeRevenue3 n (spsb3ReserveFn n r i)
      = (if r.val ≤ max (Fin.first (Fin.first i)).val
                        (max (Fin.second (Fin.first i)).val (Fin.second i).val)
         then max r.val
                  (max (min (Fin.first (Fin.first i)).val (Fin.second (Fin.first i)).val)
                       (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
                            (min (Fin.second (Fin.first i)).val (Fin.second i).val)))
         else 0)
    -- weak revenue dominance
    ∧ outcomeRevenue3 n (fpsb3ReserveFn n r i) ≥ outcomeRevenue3 n (spsb3ReserveFn n r i)
    -- exact revenue gap
    ∧ outcomeRevenue3 n (fpsb3ReserveFn n r i)
      = outcomeRevenue3 n (spsb3ReserveFn n r i)
        + (if r.val ≤ max (Fin.first (Fin.first i)).val
                          (max (Fin.second (Fin.first i)).val (Fin.second i).val)
          then max (Fin.first (Fin.first i)).val
                   (max (Fin.second (Fin.first i)).val (Fin.second i).val)
            - max r.val
                  (max (min (Fin.first (Fin.first i)).val (Fin.second (Fin.first i)).val)
                       (max (min (Fin.first (Fin.first i)).val (Fin.second i).val)
                            (min (Fin.second (Fin.first i)).val (Fin.second i).val)))
          else 0) :=
  ⟨fpsb3Reserve_revenue_eq n r i,
   spsb3Reserve_revenue_eq n r i,
   fpsb3Reserve_revenue_ge_spsb3Reserve n r i,
   fpsb3Reserve_minus_spsb3Reserve_revenue n r i⟩

end AuctionCat
