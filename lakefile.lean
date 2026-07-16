import Lake
open Lake DSL

package «auction-cat» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «kan-tactics» from git
  "https://github.com/MavenRain/kan-tactics.git" @ "3317f7a"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "498457dedc5b"

/-- Markov category foundation: symmetric monoidal categories with
    commutative comonoid structure and total morphisms.  Hosts the
    `FinStoch` and (later) `BorelStoch` instances. -/
@[default_target]
lean_lib «MarkovCat» where
  roots := #[`MarkovCat]

/-- Bayesian open games as morphisms in a Markov category, following
    Bolt-Hedges-Zahn.  Built on top of MarkovCat plus comp-cat-theory's
    Optic. -/
lean_lib «OpenGamesCat» where
  roots := #[`OpenGamesCat]

/-- Menezes-Monteiro auction theory (Chapter 2 IPV: first-price,
    second-price, Dutch, English, reserve prices) as games in
    OpenGamesCat. -/
lean_lib «AuctionCat» where
  roots := #[`AuctionCat]
