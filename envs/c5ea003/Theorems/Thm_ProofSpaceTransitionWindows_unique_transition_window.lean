-- Prove2me | Theorems.Thm_ProofSpaceTransitionWindows_unique_transition_window
-- name    : ProofSpaceTransitionWindows.unique_transition_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:17.575701+00:00
-- url     : https://prove2.me/theorems/5436c4b9-d077-4562-b3fb-bce954fabcb6
-- title:
--   Block-drift transition theorem.
-- statement:
--   **Block-drift transition theorem.** If imbalance strictly decreases between
--   successive block endpoints and is nonpositive at endpoint `K`, there is a unique
--   first sampled crossing. Every later sampled endpoint through `K` is negative.
--   Moreover, if the initial endpoint is positive, the actual sign change is
--   localized between the preceding and crossing endpoints, a window of width one
--   block.
--
--   ```lean
--   theorem ProofSpaceTransitionWindows.unique_transition_window    (f : ℕ → ℤ) (block K : ℕ)
--       (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
--       (hfinal : f (K * block) ≤ 0) :
--       ∃! k : ℕ, k ≤ K ∧ IsFirstSampledThreshold f block k ∧
--         (∀ j, k < j → j ≤ K → f (j * block) < 0) ∧
--         (0 < f 0 → 0 < k ∧
--           0 < f ((k - 1) * block) ∧ f (k * block) ≤ 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProofSpaceTransitionWindows.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProofSpaceTransitionWindows.lean#L70

-- Thm stub generated from Logic/ProofSpaceTransitionWindows.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransitionWindows

/-!
# Transition Windows from Block Drift

A pointwise decrease assumption can be too rigid for cumulative proof-space
statistics.  This file replaces it by strict negative drift only at regularly
spaced block endpoints.  The resulting theorem produces a unique first sampled
crossing, proves permanence at all later sampled endpoints, and localizes the
unsampled crossing to one block of indices.
-/

open ProofSpaceTransitionWindows

theorem ProofSpaceTransitionWindows.unique_transition_window    (f : ℕ → ℤ) (block K : ℕ)
    (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
    (hfinal : f (K * block) ≤ 0) :
    ∃! k : ℕ, k ≤ K ∧ IsFirstSampledThreshold f block k ∧
      (∀ j, k < j → j ≤ K → f (j * block) < 0) ∧
      (0 < f 0 → 0 < k ∧
        0 < f ((k - 1) * block) ∧ f (k * block) ≤ 0) := by sorry
