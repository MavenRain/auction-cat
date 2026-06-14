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
import AuctionCat.ExpectedRevenueComparison
import AuctionCat.Examples
import AuctionCat.BayesNash
import AuctionCat.Envelope
import AuctionCat.KernelTruth
import AuctionCat.KernelFirstPrice
import AuctionCat.Vickrey3
import AuctionCat.KernelFirstPrice3
import AuctionCat.ReserveTruth
import AuctionCat.Reserve3Truth
import AuctionCat.BayesNashPipeline

/-!
# AuctionCat

Menezes and Monteiro's auction theory in the Bayesian-open-games
formalism.

Contents:

- `AuctionCat.Bidder`     : `Bidder` type alias over `OpenGame` plus
                             smart constructor.
- `AuctionCat.Mechanism`  : `Mechanism` type alias for Markov morphisms.

Planned (Chapter 2 IPV):

- `FirstPriceSealedBid`, `SecondPriceSealedBid`, `Dutch`, `English` ✓
- `ReservePrice` ✓; `EntryFee` (open)
- Theorem: `Dutch ≅ FirstPriceSealedBid` ✓ — `dutch_eq_firstPrice`,
  `dutch_pipeline_eq_fpsbAuction`.
- Theorem: dominant-strategy truthfulness of `SecondPriceSealedBid` ✓
  — `vickrey_truthful_dominant`,
  `spsbAuction_truthful_is_pipeline_bayes_nash`.
- `RevenueEquivalence` ✓ at small-`n` examples (n = 3, 5 with
  half-shading); general RET gated on envelope theorem.

Extended results:

- Three-bidder framework: `FirstPriceSealedBid3`, `SecondPriceSealedBid3`,
  `Dutch3`, `English3` and BN/RET parallels at 3 bidders.
- Reserve variants for all formats at 2 and 3 bidders.
- Comparison framework: `spsb_ge_fpsb_pipeline_full` covers ten cases
  (bidder × bidder-count × reserve).  Revenue dual `fpsb_ge_spsb_revenue_main`.
- Negative results: fpsb (truthful, truthful) is not Bayes-Nash at
  n = 2, 3 under specific priors; fpsbReserve at maximal reserve gives
  trivial Bayes-Nash for every strategy pair.
-/

set_option autoImplicit false
