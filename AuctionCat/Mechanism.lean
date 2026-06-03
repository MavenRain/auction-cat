import OpenGamesCat

/-!
# AuctionCat.Mechanism

An auction mechanism converts a profile of bids into a profile of
auction outcomes (allocation + price for each participant).

In the Bayesian-open-games view, a mechanism is itself a morphism
in the underlying Markov category: it consumes the joint bid object
and produces the joint outcome object.  Composed with the parallel
combination of bidders (`OpenGame.kron`), the result is the open
game representing the full auction.

This file defines the type alias `Mechanism C Bids Outcomes` and a
small smart constructor.  Concrete instances (FirstPrice,
SecondPrice, …) live in their own files.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory

namespace AuctionCat

universe u v

/-- An auction mechanism converting a bid profile to an outcome
    profile.  In a Markov category, this is a stochastic kernel
    `Hom Bids Outcomes`. -/
def Mechanism {C : Type u} [Category.{u, v} C]
    (Bids Outcomes : C) : Type v :=
  Hom Bids Outcomes

namespace Mechanism

variable {C : Type u} [Category.{u, v} C]

/-- A mechanism from a Markov morphism. -/
def ofHom {Bids Outcomes : C} (f : Hom Bids Outcomes) :
    Mechanism Bids Outcomes := f

end Mechanism

end AuctionCat
