import AuctionCat.FirstPrice
import AuctionCat.Auction

/-!
# AuctionCat.Dutch

The Dutch (descending) auction for two bidders.

In a Dutch auction, the auctioneer announces decreasing prices and
the first bidder to accept wins, paying the announced price at the
moment of acceptance.

The standard result is that the Dutch auction is *strategically
equivalent* to a first-price sealed-bid auction: each bidder's
optimal strategy is to choose a single threshold price (the
acceptance point), and the winner is the bidder with the highest
threshold paying their own threshold.

In the open-game representation, this strategic equivalence collapses
to literal kernel equality: the Dutch mechanism on threshold-price
bids is the same morphism as `firstPriceSealedBid`.  The isomorphism
`dutch ≅ firstPriceSealedBid` is therefore an identity, recorded
below as `dutch_eq_firstPrice` for documentation and for downstream
proof reuse.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The Dutch (descending) auction mechanism for two bidders.

    Bidders submit threshold prices (the points at which they would
    accept the descending clock).  Winner = highest threshold; price =
    winner's own threshold.  Identical to first-price sealed-bid. -/
def dutchAuction (n : Nat) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  firstPriceSealedBid n

/-- Dutch auction equals first-price sealed-bid as morphisms in
    `FinStoch` — the categorical statement of strategic equivalence. -/
theorem dutch_eq_firstPrice (n : Nat) :
    dutchAuction n = firstPriceSealedBid n := rfl

/-- **Dutch ≅ FPSB at the OpenGame pipeline level**: the Dutch
    auction's pipeline form (score against truthful bidders) equals
    `fpsbAuction n`.  This is the categorical realization of the
    strategic equivalence between Dutch (descending) and first-price
    sealed-bid auctions. -/
theorem dutch_pipeline_eq_fpsbAuction (n : Nat) :
    auctionScore n (dutchAuction n) = fpsbAuction n := rfl

end AuctionCat
