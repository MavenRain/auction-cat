import AuctionCat.Bidder
import AuctionCat.Mechanism
import AuctionCat.FirstPrice
import AuctionCat.FirstPrice3
import AuctionCat.SecondPrice
import AuctionCat.SecondPrice3
import AuctionCat.Reserve

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

/-! ## Single-bidder deviator pipeline

  A variant where bidder 1 uses an arbitrary bidding strategy `bid`
  and bidder 2 stays truthful.  Used to state and prove that
  truthful spsb dominates any unilateral deviation at the OpenGame
  pipeline level. -/

/-- Two-bidder open game where bidder 1 uses strategy `bid` and
    bidder 2 is truthful. -/
def auctionGameDeviator1 (n : Nat) (bid : Fin n → Fin n) :
    OpenGame (tensorObj n n) (tensorObj n n)
             (tensorObj n n) (tensorObj (2 * n) (2 * n)) :=
  OpenGame.kron (deviatorBidder n bid) (truthfulBidder n)

/-- Score the deviator open game against a mechanism. -/
def auctionScoreDeviator1 (n : Nat) (bid : Fin n → Fin n)
    (mech : StochasticMatrix (n * n) ((2 * n) * (2 * n))) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  OpenGame.score (auctionGameDeviator1 n bid) mech

/-- Vickrey auction where bidder 1 uses strategy `bid` and bidder 2
    is truthful. -/
def spsbAuctionDeviator1 (n : Nat) (bid : Fin n → Fin n) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  auctionScoreDeviator1 n bid (secondPriceSealedBid n)

/-- Second-price-sealed-bid (Vickrey) auction with reserve price `r`
    and two truthful bidders. -/
def spsbReserveAuction (n : Nat) (r : Fin n) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  auctionScore n (spsbReserve n r)

/-- Vickrey auction with reserve price `r` where bidder 1 uses
    strategy `bid` and bidder 2 is truthful. -/
def spsbReserveAuctionDeviator1 (n : Nat) (r : Fin n) (bid : Fin n → Fin n) :
    StochasticMatrix (tensorObj n n) (tensorObj n n) :=
  auctionScoreDeviator1 n bid (spsbReserve n r)

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

/-! ## Three-bidder auction assembly

  Parallels the two-bidder `auctionGame` / `auctionScore`, but with
  three truthful bidders combined via left-associated `OpenGame.kron`
  so the result's type matches the left-associated `Fin (n * n * n)`
  convention used by `firstPriceSealedBid3` / `secondPriceSealedBid3`. -/

/-- Three truthful bidders combined via left-associated
    `OpenGame.kron`.  The result's input / output types are
    `Fin (n*n*n)` (joint valuation, joint bid, joint utility) and
    `Fin ((2*n)*(2*n)*(2*n))` (joint outcome). -/
def auctionGame3 (n : Nat) :
    OpenGame ((n * n) * n) ((n * n) * n) ((n * n) * n)
             (((2 * n) * (2 * n)) * (2 * n)) :=
  OpenGame.kron
    (OpenGame.kron (truthfulBidder n) (truthfulBidder n))
    (truthfulBidder n)

/-- The closed-form 3-bidder auction score: feed the combined
    bidders' bids into a mechanism `mech`, then run each bidder's
    utility computation.  Result is a stochastic kernel from joint
    valuations to joint utilities. -/
def auctionScore3 (n : Nat)
    (mech : StochasticMatrix (n * n * n) ((2 * n) * (2 * n) * (2 * n))) :
    StochasticMatrix ((n * n) * n) ((n * n) * n) :=
  OpenGame.score (auctionGame3 n) mech

/-- First-price-sealed-bid auction with three truthful bidders. -/
def fpsb3Auction (n : Nat) :
    StochasticMatrix ((n * n) * n) ((n * n) * n) :=
  auctionScore3 n (firstPriceSealedBid3 n)

/-- Second-price-sealed-bid (Vickrey) auction with three truthful bidders. -/
def spsb3Auction (n : Nat) :
    StochasticMatrix ((n * n) * n) ((n * n) * n) :=
  auctionScore3 n (secondPriceSealedBid3 n)

/-- Three-bidder open game where bidder 1 uses strategy `bid` and
    bidders 2, 3 are truthful. -/
def auctionGame3Deviator1 (n : Nat) (bid : Fin n → Fin n) :
    OpenGame ((n * n) * n) ((n * n) * n) ((n * n) * n)
             (((2 * n) * (2 * n)) * (2 * n)) :=
  OpenGame.kron (auctionGameDeviator1 n bid) (truthfulBidder n)

/-- Score the three-bidder deviator open game against a mechanism. -/
def auctionScoreDeviator1_3 (n : Nat) (bid : Fin n → Fin n)
    (mech : StochasticMatrix (n * n * n) ((2 * n) * (2 * n) * (2 * n))) :
    StochasticMatrix ((n * n) * n) ((n * n) * n) :=
  OpenGame.score (auctionGame3Deviator1 n bid) mech

/-- Three-bidder Vickrey auction where bidder 1 uses strategy `bid`
    and bidders 2, 3 are truthful. -/
def spsb3AuctionDeviator1 (n : Nat) (bid : Fin n → Fin n) :
    StochasticMatrix ((n * n) * n) ((n * n) * n) :=
  auctionScoreDeviator1_3 n bid (secondPriceSealedBid3 n)

end AuctionCat
