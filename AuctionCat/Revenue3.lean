import AuctionCat.FirstPrice3
import AuctionCat.SecondPrice3

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

end AuctionCat
