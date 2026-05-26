import CompCatTheory.Foundation.Category
import CompCatTheory.Foundation.Product
import CompCatTheory.Collapse.Monoidal
import CompCatTheory.Collapse.SymmetricMonoidal

/-!
# MarkovCat

A Markov category is a symmetric monoidal category in which every
object carries a commutative comonoid structure (`copy` and `discard`)
and every morphism is "total" (preserves the `discard`).

The Markov category MarkovCat formalises stochastic kernel composition
in the style of Fritz (arXiv:1908.07021): morphisms `X → Y` are
"stochastic processes" that consume a state of type `X` and produce a
state of type `Y`, possibly nondeterministically.

This is the categorical foundation for Bayesian open games downstream:
a Bayesian game is an optic in a Markov category, where the residue
object plays the role of internal state, the forward map is the
strategy producing actions, and the backward map computes utility.

Concrete instances (`FinStoch`, `BorelStoch`) live in submodules and
provide the specific stochastic structure used by the open-games
construction.
-/

set_option autoImplicit false

universe u v

open CompCatTheory
open Category Functor MonoidalCategory SymmetricMonoidalCategory

namespace MarkovCat

/-- A Markov category: a symmetric monoidal category equipped, for each
    object, with a duplication map (`copy`) and a deletion map
    (`discard`) satisfying commutative-comonoid axioms, plus the
    requirement that every morphism preserves the deletion.

    The "total morphism" property (`discard_natural`) is what makes the
    morphisms behave like stochastic kernels rather than partial
    functions: every kernel has total mass 1, so discarding the output
    is the same as discarding the input. -/
class MarkovCategory (C : Type u)
    [Category.{u, v} C]
    [MonoidalCategory C]
    [SymmetricMonoidalCategory C] where
  /-- Duplication / copy map: `X → X ⊗ X`. -/
  copy (X : C) : Hom X (X ⊗ X)

  /-- Deletion / discard map: `X → 𝟙_⊗`. -/
  discard (X : C) : Hom X tensorUnit

  /-- Coassociativity of copy: the two ways of triplicating agree. -/
  copy_coassoc (X : C) :
    copy X ≫ (𝟙 X ⊗ₕ copy X)
    = copy X ≫ (copy X ⊗ₕ 𝟙 X) ≫ associator X X X

  /-- Left counit law: copy then discard the first component is identity. -/
  copy_counit_left (X : C) :
    copy X ≫ (discard X ⊗ₕ 𝟙 X) ≫ leftUnitor X = 𝟙 X

  /-- Right counit law: copy then discard the second component is identity. -/
  copy_counit_right (X : C) :
    copy X ≫ (𝟙 X ⊗ₕ discard X) ≫ rightUnitor X = 𝟙 X

  /-- Cocommutativity: copy is symmetric under the braiding. -/
  copy_cocomm (X : C) :
    copy X ≫ braiding X X = copy X

  /-- Naturality of `discard`: every morphism is total (preserves
      total mass).  This is the defining property of a Markov category
      that distinguishes it from a general symmetric monoidal category
      with comonoids. -/
  discard_natural {X Y : C} (f : Hom X Y) :
    f ≫ discard Y = discard X

end MarkovCat
