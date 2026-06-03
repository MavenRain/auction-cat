import AuctionCat.Mechanism

/-!
# AuctionCat.FirstPrice

First-price sealed-bid auction for two bidders over `FinStoch`.

Concrete instantiation:

- Bid space  : `Fin n` for the chosen `n`.
- Per-bidder outcome  : `Fin 2 × Fin n`  (allocation in {0, 1}, price).
- Joint input  : `Fin (n * n)`.
- Joint output  : `Fin ((2 * n) * (2 * n))`.

The mechanism is a deterministic kernel (a `detMatrix`):

  fpsbFn n (i : Fin (n * n)) : Fin ((2 * n) * (2 * n))
    decodes  i ↦ (b₁, b₂)
    allocates  bidder 1 wins iff  b₁ ≥ b₂   (ties to bidder 1)
    prices    winner pays own bid; loser pays 0
    encodes the four outcome components back.

Tie-breaking convention favours bidder 1, matching the standard
first-price specification.  Loser pays 0.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for two-bidder
    first-price sealed-bid. -/
def fpsbFn (n : Nat) (i : Fin (n * n)) : Fin ((2 * n) * (2 * n)) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_left hnn
  let b1  := Fin.first i
  let b2  := Fin.second i
  let winner1 : Bool := b1.val ≥ b2.val
  let a1 : Fin 2 := if winner1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if winner1 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  let p1 : Fin n := if winner1 then b1 else ⟨0, hn⟩
  let p2 : Fin n := if winner1 then ⟨0, hn⟩ else b2
  Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)

/-- The first-price sealed-bid mechanism over `FinStoch` for two
    bidders with bid space `Fin n`. -/
def firstPriceSealedBid (n : Nat) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  detMatrix (fpsbFn n)

end AuctionCat
