import OpenGamesCat

/-!
# AuctionCat.Bidder

A bidder in an auction is an open game converting a private valuation
to a bid, then receiving an auction outcome (allocation and price)
that determines its utility.

In the Bayesian-open-games view:

  Bidder V U B A = OpenGame V U B A

with the four type parameters interpreted as:

  V : valuation type    (input: the bidder's private type)
  U : utility type      (backward output: utility / payoff)
  B : bid type          (forward output: the bid submitted)
  A : auction outcome   (backward input: allocation and price)

The internal state `M` of the underlying optic carries any
information the bidder needs to forward from "submit-bid" time
to "receive-outcome" time — typically the valuation itself.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory

namespace AuctionCat

universe u v

/-- A bidder in an auction as an open game `V → (U, B, A)`. -/
def Bidder {C : Type u} [Category.{u, v} C] [MonoidalCategory C]
    (V U B A : C) : Type max u v :=
  OpenGamesCat.OpenGame V U B A

namespace Bidder

variable {C : Type u} [Category.{u, v} C] [MonoidalCategory C]

/-- Build a bidder from an explicit strategy and utility function.
    The internal state is taken to be the valuation type `V` itself
    — the bidder forwards the valuation from bidding time to
    outcome-evaluation time. -/
def make {V U B A : C}
    (strategy : Hom V (tensorObj V B))
    (utility : Hom (tensorObj V A) U) : Bidder V U B A where
  M := V
  view := strategy
  update := utility

end Bidder

end AuctionCat
