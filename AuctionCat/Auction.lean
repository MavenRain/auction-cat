import AuctionCat.Bidder
import AuctionCat.Mechanism
import AuctionCat.FirstPrice
import AuctionCat.SecondPrice

/-!
# AuctionCat.Auction

Full two-bidder auction assembly over `FinStoch`.

Combines the monoidal product of two truthful bidders with an
auction mechanism via `OpenGame.score`, producing the closed-form
"valuations to utilities" stochastic kernel for the complete game.

  auctionGame n : OpenGame (n*n) (n*n) (n*n) ((2*n)*(2*n))
                = truthfulBidder n ⊗ₒ truthfulBidder n

  auctionScore n mech : StochasticMatrix (n*n) (n*n)
                      = score (auctionGame n) mech

Concrete instantiations for first-price and second-price are given.
-/

set_option autoImplicit false

open CompCatTheory OpenGamesCat
open Category Functor MonoidalCategory SymmetricMonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Two truthful bidders combined via the monoidal product. -/
def auctionGame (n : Nat) :
    OpenGame (tensorObj n n) (tensorObj n n)
             (tensorObj n n) (tensorObj (2 * n) (2 * n)) :=
  OpenGame.kron (truthfulBidder n) (truthfulBidder n)

/-- The closed-form auction score: feed the combined bidders' bids
    into a mechanism `mech`, then run the bidders' utility
    computations on the outcomes.  Result is a stochastic kernel
    from joint valuations to joint utilities. -/
def auctionScore (n : Nat)
    (mech : StochasticMatrix (n * n) ((2 * n) * (2 * n))) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  OpenGame.score (auctionGame n) mech

/-- First-price-sealed-bid auction with two truthful bidders. -/
def fpsbAuction (n : Nat) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  auctionScore n (firstPriceSealedBid n)

/-- Second-price-sealed-bid (Vickrey) auction with two truthful bidders. -/
def spsbAuction (n : Nat) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  auctionScore n (secondPriceSealedBid n)

/-! ## Mechanism + paired bidding strategy

  Composes a deterministic strategy for each of the two bidders with
  a mechanism, giving the joint-valuation-to-joint-outcome kernel
  for the resulting open game when those strategies are used. -/

/-- Compose paired deterministic strategies `bid1`, `bid2` with a
    mechanism `mech` to obtain a joint-valuation-to-joint-outcome
    kernel.  Joint valuations enter, each bidder transforms their
    valuation through their strategy, the resulting joint bids feed
    into the mechanism, and joint outcomes come out. -/
def biddedMechanism (n : Nat) (bid1 bid2 : Fin n → Fin n)
    (mech : StochasticMatrix (n * n) ((2 * n) * (2 * n))) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  (StochasticMatrix.kron (detMatrix bid1) (detMatrix bid2)).comp mech

/-! ## Generic n-bidder open game

  Using `OpenGame.iterKron`, we can combine an arbitrary number of
  truthful bidders into a single open game.  The result's types
  involve iterated tensor products `tensorPowObj` rather than the
  hard-coded `tensorObj n n`, so it's polymorphic in the bidder
  count. -/

/-- An n-bidder open game where every bidder is a truthful bidder
    over `Fin valuationSize` valuations. -/
def truthfulAuctionN (valuationSize numBidders : Nat) :
    OpenGame (tensorPowObj valuationSize numBidders)
             (tensorPowObj valuationSize numBidders)
             (tensorPowObj valuationSize numBidders)
             (tensorPowObj (2 * valuationSize) numBidders) :=
  OpenGame.iterKron (truthfulBidder valuationSize) numBidders

end AuctionCat
