import AuctionCat.SecondPrice

/-!
# AuctionCat.English

The English (ascending) auction for two bidders.

In an English auction, the auctioneer announces increasing prices and
bidders drop out when the price exceeds their willingness to pay.
The last remaining bidder wins and pays the dropout price of the
second-to-last bidder.

For two bidders this is strategically equivalent to a second-price
sealed-bid (Vickrey) auction: each bidder's optimal strategy is to
choose a single dropout price, and the winner pays the loser's
dropout price.  Truthful dropout (drop out at one's valuation) is the
dominant strategy, mirroring the Vickrey theorem in
`AuctionCat.SecondPrice`.

In the open-game representation, this strategic equivalence collapses
to literal kernel equality: the English mechanism on dropout-price
bids is the same morphism as `secondPriceSealedBid`.  Recorded below
as `english_eq_secondPrice`.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The English (ascending) auction mechanism for two bidders.

    Bidders submit dropout prices.  Winner = highest dropout; price =
    loser's dropout.  Identical to second-price sealed-bid (Vickrey). -/
def englishAuction (n : Nat) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  secondPriceSealedBid n

/-- English auction equals second-price sealed-bid (Vickrey) as
    morphisms in `FinStoch` — the categorical statement of strategic
    equivalence. -/
theorem english_eq_secondPrice (n : Nat) :
    englishAuction n = secondPriceSealedBid n := rfl

end AuctionCat
