import AuctionCat.FirstPrice
import AuctionCat.SecondPrice

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

end AuctionCat
