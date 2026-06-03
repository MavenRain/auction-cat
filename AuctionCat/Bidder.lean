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
open MarkovCat.FinStoch

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

/-! ## Concrete bidders over FinStoch -/

/-- The utility function for a "truthful" bidder over `Fin n`
    valuations and a `Fin (2 * n)` per-bidder outcome
    (allocation × price).

    Utility = (valuation - price) if won, else 0.  Uses Nat
    truncated subtraction, capped within `Fin n`. -/
def truthfulUtilityFn (n : Nat) (x : Fin (n * (2 * n))) : Fin n :=
  let hn2n : 0 < n * (2 * n) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  let hn : 0 < n := Nat.pos_of_mul_pos_right hn2n
  let v := Fin.first x
  let outcome := Fin.second x
  let a := Fin.first outcome
  let p := Fin.second outcome
  if a.val = 1 then
    ⟨v.val - p.val, by have := v.isLt; omega⟩
  else
    ⟨0, hn⟩

/-- A truthful bidder over `Fin n` valuations: bid your valuation.

    Strategy is `copy n : Fin n → Fin (n * n)` (the diagonal map
    in `FinStoch`), so the bid equals the valuation.  Utility uses
    `truthfulUtilityFn`. -/
def truthfulBidder (n : Nat) : Bidder n n n (2 * n) :=
  Bidder.make (copy n) (detMatrix (truthfulUtilityFn n))

end AuctionCat
