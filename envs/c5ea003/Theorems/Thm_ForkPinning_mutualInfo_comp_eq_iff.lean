-- Prove2me | Theorems.Thm_ForkPinning_mutualInfo_comp_eq_iff
-- name    : ForkPinning.mutualInfo_comp_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:33.317853+00:00
-- url     : https://prove2.me/theorems/3a8d728b-2c13-44e3-89ca-d9b318202c55
-- title:
--   Equality in data processing detects sufficiency.
-- statement:
--   **Equality in data processing detects sufficiency.**  The coarse observable `g ∘ X` retains
--   *all* of the information `X` has about the fork exactly when every fine cell of the joint law is
--   the corresponding coarse cell rescaled — i.e. when `g ∘ X` is a sufficient statistic for `Y`.
--
--   ```lean
--   theorem ForkPinning.mutualInfo_comp_eq_iff(g : κ → κ') (X : Ω → κ) (Y : Ω → β) :
--       mutualInfo (fun ω => g (X ω)) Y = mutualInfo X Y
--         ↔ ∀ k b, prb (joint X Y) (k, b)
--             = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k
--                 / prb (fun ω => g (X ω)) (g k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningDataProcessing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningDataProcessing.lean#L352

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

theorem ForkPinning.mutualInfo_comp_eq_iff(g : κ → κ') (X : Ω → κ) (Y : Ω → β) :
    mutualInfo (fun ω => g (X ω)) Y = mutualInfo X Y
      ↔ ∀ k b, prb (joint X Y) (k, b)
          = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k
              / prb (fun ω => g (X ω)) (g k) := by sorry
