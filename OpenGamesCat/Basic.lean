import MarkovCat
import CompCatTheory.Collapse.Optic

/-!
# OpenGamesCat.Basic

A Bayesian open game from `(X, S)` to `(Y, R)` over a Markov category
`C` is an optic in `C`: a representative `⟨M, view, update⟩` where

  view   : Hom X (M ⊗ Y)        -- forward channel: input to state + output
  update : Hom (M ⊗ R) S        -- backward channel: state + continuation
                                   to feedback

For Bayesian open games specifically, `C` is assumed to be a Markov
category (so morphisms are stochastic kernels rather than partial
functions) — this is the central distinction from Hedges' original
"open games" (which lived in a category with negation).

The data of an open game is therefore literally that of an optic.
Equilibrium and best-response play out as separate predicates over
the surrounding context (defined in later files).
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory SymmetricMonoidalCategory

namespace OpenGamesCat

universe u v

/-- A Bayesian open game from `(X, S)` to `(Y, R)` over a Markov
    category `C`: literally an optic in `C`.

    Marked `@[reducible]` so the existing `Optic.id` and `Optic.comp`
    flow through, giving us the category structure on open games
    for free (modulo dinaturality, which is deferred). -/
@[reducible]
def OpenGame {C : Type u} [Category.{u, v} C] [MonoidalCategory C]
    (X S Y R : C) : Type max u v :=
  Optic X S Y R

namespace OpenGame

variable {C : Type u} [Category.{u, v} C] [MonoidalCategory C]

/-- The identity open game on `(X, S)`: pass input through, return
    continuation unchanged.  Internal state is the tensor unit. -/
def id (X S : C) : OpenGame X S X S := Optic.id X S

/-- Sequential composition of two open games: chain the forward
    channels, chain the backward channels in reverse.  Internal state
    is the tensor product of the two internal states. -/
def comp {X S Y R Z Q : C}
    (f : OpenGame X S Y R) (g : OpenGame Y R Z Q) : OpenGame X S Z Q :=
  Optic.comp f g

scoped infixr:80 " ≫ₒ " => OpenGame.comp

end OpenGame

/-! ## Middle interchange

  The "middle-four interchange" `(A ⊗ B) ⊗ (D ⊗ E) → (A ⊗ D) ⊗ (B ⊗ E)`
  swaps the middle pair via braiding.  Used by `OpenGame.kron` to rearrange
  the parallel composition of two optics' views and updates. -/

/-- Middle-four interchange in a symmetric monoidal category. -/
def middleInterchange {C : Type u} [Category.{u, v} C]
    [MonoidalCategory C] [SymmetricMonoidalCategory C] (A B D E : C) :
    Hom (tensorObj (tensorObj A B) (tensorObj D E))
        (tensorObj (tensorObj A D) (tensorObj B E)) :=
  associator A B (tensorObj D E)
    ≫ tensorHom (𝟙 A) (associatorInv B D E)
    ≫ tensorHom (𝟙 A) (tensorHom (braiding B D) (𝟙 E))
    ≫ tensorHom (𝟙 A) (associator D B E)
    ≫ associatorInv A D (tensorObj B E)

/-! ## Monoidal product of open games

  Two open games can be combined into one by tensoring their data and
  rearranging the result via the middle-four interchange.  This models
  simultaneous play: two independent open games are played in
  parallel, with no information flow between them. -/

namespace OpenGame

variable {C : Type u} [Category.{u, v} C]
  [MonoidalCategory C] [SymmetricMonoidalCategory C]

/-- Monoidal product of open games:
    `(f ⊗ₒ g) : OpenGame (X ⊗ X') (S ⊗ S') (Y ⊗ Y') (R ⊗ R')`. -/
def kron {X S Y R X' S' Y' R' : C}
    (f : OpenGame X S Y R) (g : OpenGame X' S' Y' R') :
    OpenGame (tensorObj X X') (tensorObj S S')
             (tensorObj Y Y') (tensorObj R R') where
  M := tensorObj f.M g.M
  view :=
    tensorHom f.view g.view
      ≫ middleInterchange f.M Y g.M Y'
  update :=
    middleInterchange f.M g.M R R'
      ≫ tensorHom f.update g.update

scoped infixr:75 " ⊗ₒ " => OpenGame.kron

end OpenGame

end OpenGamesCat
