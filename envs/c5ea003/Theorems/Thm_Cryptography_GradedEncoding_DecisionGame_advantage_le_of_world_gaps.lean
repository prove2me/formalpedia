-- Prove2me | Theorems.Thm_Cryptography_GradedEncoding_DecisionGame_advantage_le_of_world_gaps
-- name    : Cryptography.GradedEncoding.DecisionGame.advantage_le_of_world_gaps
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:18:50.746183+00:00
-- url     : https://prove2.me/theorems/0d26aee1-a360-4e07-92ad-f92b52aeefb8
-- title:
--   Approximate game-hop theorem.
-- statement:
--   **Approximate game-hop theorem.** If corresponding worlds of two games are
--   within `δfalse` and `δtrue` in `ℓ¹` distance, then every deterministic
--   adversary's target advantage is at most its source advantage plus those two
--   simulation errors.
--
--   ```lean
--   theorem Cryptography.GradedEncoding.DecisionGame.advantage_le_of_world_gaps{Ω : Type*} [Fintype Ω]
--       (source target : DecisionGame Ω) (A : Ω → Bool) (δfalse δtrue : ℝ)
--       (hfalse : LWEOperational.l1Gap
--         (target.experiment.challenge false)
--         (source.experiment.challenge false) ≤ δfalse)
--       (htrue : LWEOperational.l1Gap
--         (target.experiment.challenge true)
--         (source.experiment.challenge true) ≤ δtrue) :
--       target.advantage A ≤ source.advantage A + δfalse + δtrue := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/GradedEncoding/SecurityReduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/GradedEncoding/SecurityReduction.lean#L107

-- Thm stub generated from Cryptography/GradedEncoding/SecurityReduction.lean
import Mathlib
import Definitions.Def_Cryptography_GradedEncoding_Foundations
import Definitions.Def_Cryptography_GradedEncoding_SecurityReduction
import Definitions.Def_Cryptography_LWE_OperationalSecurity

/-!
# Security reductions for multilinear graded encodings

The reduction layer is independent of any particular graded-encoding candidate.
A decisional multilinear Diffie--Hellman game is represented by its two finite
transcript distributions. A perfect reduction is an equivalence of transcript
spaces preserving both distributions pointwise. The main theorem proves exact
preservation of every deterministic distinguisher's advantage and transfers any
source hardness bound to the graded target game.
-/

-- open removed: section is not a namespace

noncomputable section

open Cryptography.GradedEncoding


open DecisionGame

variable {Ω : Type*} [Fintype Ω]





variable {Source Target : Type*} [Fintype Source] [Fintype Target]


open PerfectReduction

variable {source : DecisionGame Source} {target : DecisionGame Target}







open DecisionGame

theorem Cryptography.GradedEncoding.DecisionGame.advantage_le_of_world_gaps{Ω : Type*} [Fintype Ω]
    (source target : DecisionGame Ω) (A : Ω → Bool) (δfalse δtrue : ℝ)
    (hfalse : LWEOperational.l1Gap
      (target.experiment.challenge false)
      (source.experiment.challenge false) ≤ δfalse)
    (htrue : LWEOperational.l1Gap
      (target.experiment.challenge true)
      (source.experiment.challenge true) ≤ δtrue) :
    target.advantage A ≤ source.advantage A + δfalse + δtrue := by sorry
