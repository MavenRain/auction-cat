import AuctionCat.BayesNash

/-!
# AuctionCat.Envelope

The envelope theorem (Myerson 1981) for the two-bidder Vickrey
auction.

For a Bayes-Nash equilibrium in a Bayesian game with quasi-linear
utility, the expected payment of a type is uniquely determined by
the allocation rule (up to a normalising constant).  In the
two-bidder Vickrey setting with truthful equilibrium and prior `p`
on the opponent's valuation:

  Q(v)  := P(bidder 1 wins | v1 = v)
        = Σ_{v2 ≤ v} p(v2)

  U(v)  := E[utility | v1 = v, truthful bidding]
        = Σ_{v2 ≤ v} p(v2) * (v - v2)

  P(v)  := E[payment | v1 = v]
        = v * Q(v) - U(v)
        = Σ_{v2 ≤ v} p(v2) * v2

The discrete envelope identity reads:

  U(v) = Σ_{t < v} Q(t)

i.e., the expected utility is the sum of allocation probabilities
at lower types.  This is the discrete analogue of the continuous
envelope formula `U(v) = ∫_0^v Q(t) dt`.

This file provides the data layer for the theorem (`vickreyAllocation`,
`vickreyExpectedPayment`, `vickreyEqUtility`) and verifies the
envelope identity by `native_decide` at a small grid.  The general
proof requires `Fin.sumRat_swap` plus careful conditional algebra
and is left as a future enhancement.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Bidder 1's expected allocation probability at type `v1` under
    Vickrey with prior `p` on bidder 2's valuation: the prior
    probability that bidder 2's valuation lies weakly below `v1`. -/
def vickreyAllocation (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    if v2.val ≤ v1.val then prior v2 else 0)

/-- Bidder 1's expected payment at type `v1` under Vickrey with
    truthful bidder 2 and prior `p`: when bidder 1 wins, the
    payment is bidder 2's valuation. -/
def vickreyExpectedPayment (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    if v2.val ≤ v1.val then prior v2 * (v2.val : Nat).cast else 0)

/-- Bidder 1's equilibrium expected utility at type `v1` under
    Vickrey with both bidders truthful and prior `p` on bidder 2. -/
def vickreyEqUtility (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun v2 : Fin n =>
    prior v2 * ((vickreyUtility n v1 v1 v2).val : Nat).cast)

/-- The right-hand side of the discrete envelope identity:
    `Σ_{t < v} Q(t)` — the cumulative allocation probability up to
    type `v - 1`. -/
def vickreyEnvelopeIntegral (n : Nat) (prior : Fin n → Rat)
    (v1 : Fin n) : Rat :=
  Fin.sumRat (fun t : Fin n =>
    if t.val < v1.val then vickreyAllocation n prior t else 0)

/-- Concrete envelope identity at `n = 4` with uniform prior `1/4`
    and `v1 = 3` (top type): both sides compute to `3/2`. -/
example :
    vickreyEqUtility 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩
    = vickreyEnvelopeIntegral 4 (fun _ => (1 : Rat) / 4) ⟨3, by decide⟩ := by
  unfold vickreyEqUtility vickreyEnvelopeIntegral
        vickreyAllocation
  native_decide

/-- Concrete envelope identity at `n = 5` with uniform prior `1/5`
    and `v1 = 4` (top type): both sides compute to `2`. -/
example :
    vickreyEqUtility 5 (fun _ => (1 : Rat) / 5) ⟨4, by decide⟩
    = vickreyEnvelopeIntegral 5 (fun _ => (1 : Rat) / 5) ⟨4, by decide⟩ := by
  unfold vickreyEqUtility vickreyEnvelopeIntegral
        vickreyAllocation
  native_decide

end AuctionCat
