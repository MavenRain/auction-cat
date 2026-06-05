import AuctionCat.SecondPrice
import AuctionCat.Auction

/-!
# AuctionCat.KernelTruth

Lifts the bidder-level Vickrey truthfulness theorem
(`spsb_bidder1_truthful_dominates` from `SecondPrice.lean`) to the
StochasticMatrix kernel level.

The bidder-level theorem says: for any deviation strategy `bid`,
truthful bidding gives bidder 1 at least as much utility as
bidding `bid v1`, at every realised opposing valuation `v2`.

The kernel-level theorem says the same thing in terms of the
`spsbAuction` kernel's expected bidder-1 utility: for any
deviation strategy applied to bidder 1, the resulting closed-form
auction kernel yields a bidder-1 expected utility (computed via
the kernel's row distribution on `Fin (n * n)` outputs) that is at
most the truthful auction's bidder-1 expected utility.

For deterministic kernels (which `spsbAuction n` is, by
construction), the expected utility collapses to the deterministic
output's bidder-1 component cast to `Rat`.  This file provides:

  - `auctionBidder1Util`: expected bidder-1 utility of any auction
    kernel at a joint valuation profile.
  - `auctionBidder1Util_det`: collapses to the deterministic output
    component when the kernel is a `detMatrix`.

The final connection from `spsbAuction n` to a specific deterministic
function is left for a follow-on: it requires unfolding `auctionGame`
+ `OpenGame.kron` + `OpenGame.score` through the optic pipeline.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- The expected bidder-1 utility of an auction kernel `auction` at
    joint valuation `v_joint`: sum over joint utility outputs
    weighted by the kernel's row probability, projecting to bidder
    1's component. -/
def auctionBidder1Util (n : Nat)
    (auction : StochasticMatrix (n * n) (n * n))
    (v_joint : Fin (n * n)) : Rat :=
  Fin.sumRat (fun u_joint : Fin (n * n) =>
    auction.entry v_joint u_joint
    * ((Fin.first u_joint).val : Nat).cast)

/-- For deterministic kernels (a `detMatrix` of some underlying
    function `f`), the expected bidder-1 utility is the cast of
    `Fin.first (f v_joint).val`.  The `kron`-style sum collapses
    via `sumRat_kron_mul`. -/
theorem auctionBidder1Util_det (n : Nat)
    (f : Fin (n * n) → Fin (n * n)) (v_joint : Fin (n * n)) :
    auctionBidder1Util n (detMatrix f) v_joint
    = ((Fin.first (f v_joint)).val : Nat).cast := by
  unfold auctionBidder1Util
  show Fin.sumRat (fun u_joint : Fin (n * n) =>
        kron (f v_joint) u_joint
        * ((Fin.first u_joint).val : Nat).cast)
      = ((Fin.first (f v_joint)).val : Nat).cast
  exact sumRat_kron_mul (f v_joint)
    (fun u : Fin (n * n) => ((Fin.first u).val : Nat).cast)

/-- The deterministic outcome of `spsbAuction n` at joint valuation
    `(v1, v2)` (both bidders truthful): bidder 1 gets
    `vickreyUtility n v1 v1 v2`, bidder 2 gets
    `vickreyUtility n v2 v2 v1`. -/
def spsbAuctionFn (n : Nat) (v_joint : Fin (n * n)) : Fin (n * n) :=
  Fin.pair
    (vickreyUtility n (Fin.first v_joint) (Fin.first v_joint)
                      (Fin.second v_joint))
    (vickreyUtility n (Fin.second v_joint) (Fin.second v_joint)
                      (Fin.first v_joint))

/-- The deterministic outcome of `spsbAuctionDeviator1` at joint
    valuation `(v1, v2)` (bidder 1 uses `bid`, bidder 2 truthful):
    bidder 1's utility uses `bid v1` as their submitted bid,
    bidder 2's utility uses `bid v1` as their opponent's bid. -/
def spsbAuctionDeviator1Fn (n : Nat) (bid : Fin n → Fin n)
    (v_joint : Fin (n * n)) : Fin (n * n) :=
  Fin.pair
    (vickreyUtility n (Fin.first v_joint) (bid (Fin.first v_joint))
                      (Fin.second v_joint))
    (vickreyUtility n (Fin.second v_joint) (Fin.second v_joint)
                      (bid (Fin.first v_joint)))

/-- **Kernel-level Vickrey truthfulness** (at the deterministic
    outcome-function level).  Bidder 1's expected utility in the
    truthful `spsbAuction` kernel weakly dominates bidder 1's
    expected utility in any single-deviator variant.

    Stated against the deterministic underlying functions
    `spsbAuctionFn` and `spsbAuctionDeviator1Fn` (which describe
    the closed-form outcomes); connecting these to the open-game
    pipeline definitions of `spsbAuction` / `spsbAuctionDeviator1`
    is a separate (substantial) unfolding step. -/
theorem spsb_bidder1_kernel_dominance (n : Nat) (bid : Fin n → Fin n)
    (v_joint : Fin (n * n)) :
    auctionBidder1Util n (detMatrix (spsbAuctionFn n)) v_joint
    ≥ auctionBidder1Util n (detMatrix (spsbAuctionDeviator1Fn n bid))
                            v_joint := by
  rw [auctionBidder1Util_det, auctionBidder1Util_det]
  show ((Fin.first (spsbAuctionFn n v_joint)).val : Nat).cast
       ≥ ((Fin.first (spsbAuctionDeviator1Fn n bid v_joint)).val
            : Nat).cast
  unfold spsbAuctionFn spsbAuctionDeviator1Fn
  have hv1 : 0 < n * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) v_joint.isLt
  have hn : 0 < n := Nat.pos_of_mul_pos_right hv1
  have h2n : 0 < 2 := by decide
  rw [Fin.first_pair, Fin.first_pair]
  -- Now: cast (vickreyUtility n v1 v1 v2).val ≥ cast (vickreyUtility n v1 (bid v1) v2).val
  have h_util := vickrey_truthful_dominant n (Fin.first v_joint)
                   (bid (Fin.first v_joint)) (Fin.second v_joint)
  exact_mod_cast h_util

/-! ## Open-game-pipeline reductions (toward `spsbAuction = detMatrix spsbAuctionFn`)

  This block builds toward the connection from `spsbAuction n`
  (defined via the OpenGame pipeline as `score (auctionGame n)
  (secondPriceSealedBid n)`) to its explicit deterministic
  underlying function `spsbAuctionFn n`.

  The proof structure walks the composition
    view ≫ tensorHom (𝟙 M) mech ≫ update
  with each piece a detMatrix; `detMatrix_comp` + `kron_detMatrix`
  collapse the composition to a single detMatrix.  Identifying the
  underlying function as `spsbAuctionFn n` requires computing
  `(auctionGame n).view` and `(auctionGame n).update` explicitly. -/

/-- Tensor of two `copy` kernels (the view side of two truthful
    bidders before middle-interchange): each copies its input to
    a diagonal pair, then the pair-of-diagonals is exposed. -/
theorem kron_copy_copy (n : Nat) :
    StochasticMatrix.kron (copy n) (copy n)
    = detMatrix (fun x : Fin (n * n) =>
        Fin.pair (Fin.pair (Fin.first x) (Fin.first x))
                 (Fin.pair (Fin.second x) (Fin.second x))) := by
  show StochasticMatrix.kron (detMatrix copyFin) (detMatrix copyFin) = _
  rw [kron_detMatrix]
  rfl

/-- The deterministic underlying function of the middle-four
    interchange `((A ⊗ B) ⊗ (D ⊗ E)) → ((A ⊗ D) ⊗ (B ⊗ E))`: send
    `((a, b), (d, e))` to `((a, d), (b, e))`. -/
def middleInterchangeFn (A B D E : Nat) (x : Fin ((A * B) * (D * E))) :
    Fin ((A * D) * (B * E)) :=
  Fin.pair
    (Fin.pair (Fin.first (Fin.first x)) (Fin.first (Fin.second x)))
    (Fin.pair (Fin.second (Fin.first x)) (Fin.second (Fin.second x)))

/-- `OpenGamesCat.middleInterchange` (in `FinStoch`) equals the
    deterministic kernel of `middleInterchangeFn`.  Proved
    structurally by decomposing `x` into its nested pair form and
    pushing the five-step composition through `associatorFin_pair`,
    `associatorInvFin_pair`, and `braidingFin_pair`. -/
theorem middleInterchange_eq_detMatrix (A B D E : Nat) :
    (OpenGamesCat.middleInterchange A B D E :
        StochasticMatrix ((A * B) * (D * E)) ((A * D) * (B * E)))
    = detMatrix (middleInterchangeFn A B D E) := by
  unfold OpenGamesCat.middleInterchange
  -- Unfold typeclass-level tensorHom/𝟙/associator/braiding to FinStoch
  show (MarkovCat.FinStoch.associator A B (D * E)).comp
        ((StochasticMatrix.kron (MarkovCat.FinStoch.idMatrix A)
            (MarkovCat.FinStoch.associatorInv B D E)).comp
          ((StochasticMatrix.kron (MarkovCat.FinStoch.idMatrix A)
              (StochasticMatrix.kron (MarkovCat.FinStoch.braiding B D)
                (MarkovCat.FinStoch.idMatrix E))).comp
            ((StochasticMatrix.kron (MarkovCat.FinStoch.idMatrix A)
                (MarkovCat.FinStoch.associator D B E)).comp
              (MarkovCat.FinStoch.associatorInv A D (B * E)))))
       = detMatrix (middleInterchangeFn A B D E)
  rw [associator_eq_detMatrix A B (D * E),
      idMatrix_eq_detMatrix A,
      associatorInv_eq_detMatrix B D E,
      braiding_eq_detMatrix B D,
      idMatrix_eq_detMatrix E,
      kron_detMatrix,
      kron_detMatrix,
      associator_eq_detMatrix D B E,
      kron_detMatrix,
      associatorInv_eq_detMatrix A D (B * E),
      kron_detMatrix]
  rw [detMatrix_comp, detMatrix_comp, detMatrix_comp, detMatrix_comp]
  congr 1
  funext x
  have hABDE : 0 < (A * B) * (D * E) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hAB : 0 < A * B := Nat.pos_of_mul_pos_right hABDE
  have hDE : 0 < D * E := Nat.pos_of_mul_pos_left hABDE
  have hA : 0 < A := Nat.pos_of_mul_pos_right hAB
  have hB : 0 < B := Nat.pos_of_mul_pos_left hAB
  have hD : 0 < D := Nat.pos_of_mul_pos_right hDE
  have hBD : 0 < B * D := Nat.mul_pos hB hD
  have hx : x = Fin.pair (Fin.pair (Fin.first (Fin.first x))
                                    (Fin.second (Fin.first x)))
                          (Fin.pair (Fin.first (Fin.second x))
                                    (Fin.second (Fin.second x))) := by
    rw [Fin.pair_first_second (Fin.first x),
        Fin.pair_first_second (Fin.second x)]
    exact (Fin.pair_first_second x).symm
  rw [hx]
  unfold middleInterchangeFn
  simp only [associatorFin_pair, associatorInvFin_pair, braidingFin_pair,
             Fin.first_pair, Fin.second_pair hA,
             Fin.second_pair hD, Fin.second_pair hAB,
             Fin.second_pair hBD]

end AuctionCat
