import AuctionCat.Bidder
import AuctionCat.Mechanism
import AuctionCat.FirstPrice
import AuctionCat.FirstPrice3
import AuctionCat.SecondPrice
import AuctionCat.SecondPrice3
import AuctionCat.Dutch
import AuctionCat.Dutch3
import AuctionCat.English
import AuctionCat.English3
import AuctionCat.Reserve
import AuctionCat.Auction
import AuctionCat.Revenue
import AuctionCat.Revenue3
import AuctionCat.Examples
import AuctionCat.BayesNash
import AuctionCat.Envelope
import AuctionCat.KernelTruth
import AuctionCat.Vickrey3

/-!
# AuctionCat

Menezes and Monteiro's auction theory in the Bayesian-open-games
formalism.

Contents:

- `AuctionCat.Bidder`     : `Bidder` type alias over `OpenGame` plus
                             smart constructor.
- `AuctionCat.Mechanism`  : `Mechanism` type alias for Markov morphisms.

Planned (Chapter 2 IPV):

- `FirstPriceSealedBid`, `SecondPriceSealedBid`, `Dutch`, `English`
- `ReservePrice`, `EntryFee`
- Theorem: `Dutch ≅ FirstPriceSealedBid` (iso of open games)
- Theorem: dominant-strategy truthfulness of `SecondPriceSealedBid`
- `RevenueEquivalence` (proof gated on envelope theorem)
-/

set_option autoImplicit false
