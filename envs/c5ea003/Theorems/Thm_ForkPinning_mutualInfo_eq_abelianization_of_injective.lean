-- Prove2me | Theorems.Thm_ForkPinning_mutualInfo_eq_abelianization_of_injective
-- name    : ForkPinning.mutualInfo_eq_abelianization_of_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:48.286513+00:00
-- url     : https://prove2.me/theorems/03737437-cd9a-4243-9feb-6c32e14ed133
-- title:
--   An injective character is exactly as good as the abelianization.
-- statement:
--   **An injective character is exactly as good as the abelianization.**  If the character
--   `f : G →* A` induces an injective map on `G^ab` (equivalently, its kernel is precisely the
--   commutator subgroup), then it extracts the full abelian information about every fork.
--
--   ```lean
--   theorem ForkPinning.mutualInfo_eq_abelianization_of_injective(f : G →* A) (Y : G → β)
--       (hinj : Function.Injective (Abelianization.lift f)) :
--       mutualInfo (fun g : G => f g) Y = mutualInfo (fun g : G => Abelianization.of g) Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningDataProcessing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningDataProcessing.lean#L406

-- Thm stub generated from Probability/ForkPinningDataProcessing.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningDataProcessing
import Definitions.Def_Probability_ForkPinningGalois
/-
# Coarsening a character can only lose information (data processing), and the
# abelianization is the optimal congruence observable

The fork-pinning criterion says *which* forks a Dirichlet character can pin.  This file makes
the criterion **quantitative**: information about a fork can never be created by post-processing
the observable, so among all abelian characters of the Galois group the abelianization map
`G → G^ab` is the unique optimum:

* `ForkPinning.mutualInfo_comp_le` : the data-processing inequality
  `I(g ∘ X ; Y) ≤ I(X ; Y)` for the uniform measure on a finite space;
* `ForkPinning.mutualInfo_le_of_determines` : a coarser statistic carries less information;
* `ForkPinning.mutualInfo_le_abelianization` : **every** Dirichlet character `f : G →* A`
  satisfies `I(f ; Y) ≤ I(G^ab ; Y)` — no abelian character can beat the abelianization;
* `ForkPinning.abelianization_is_optimal` : the resulting sharp capacity statement, that the
  supremum over abelian characters of the pinned information is attained at `G^ab`.

The proof of the data-processing inequality is a grouped Gibbs argument: writing
`r = P(X = k, Y = b)`, `p = P(X = k)`, `q = P(gX = gk, Y = b)`, `P = P(gX = gk)`, the
elementary inequality `r log r − r log (q p / P) ≥ r − q p / P` is summed over all `(k, b)`;
the right-hand side telescopes to `0` and the left-hand side is exactly `I(X;Y) − I(gX;Y)`.
-/


open ForkPinning

open Finset Real

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ κ' β : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype β] [DecidableEq β]

/-! ## Fibres of a post-processed statistic -/







/-! ## The elementary Gibbs term of the data-processing inequality -/


/-! ## The four sum identities -/






/-! ## The data-processing inequality -/










/-! ## The abelianization is the optimal congruence observable -/


variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
variable [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]


omit [DecidableEq G] in

theorem ForkPinning.mutualInfo_eq_abelianization_of_injective(f : G →* A) (Y : G → β)
    (hinj : Function.Injective (Abelianization.lift f)) :
    mutualInfo (fun g : G => f g) Y = mutualInfo (fun g : G => Abelianization.of g) Y := by sorry
