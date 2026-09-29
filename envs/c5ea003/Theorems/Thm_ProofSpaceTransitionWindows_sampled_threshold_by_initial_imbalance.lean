-- Prove2me | Theorems.Thm_ProofSpaceTransitionWindows_sampled_threshold_by_initial_imbalance
-- name    : ProofSpaceTransitionWindows.sampled_threshold_by_initial_imbalance
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:10.542919+00:00
-- url     : https://prove2.me/theorems/eea7a8e5-e7ff-486e-ad18-c46787ca9db2
-- title:
--   If the number of sampled blocks is at least the initial integer imbalance,
-- statement:
--   If the number of sampled blocks is at least the initial integer imbalance,
--   then a sampled threshold must occur by the final endpoint.
--
--   ```lean
--   theorem ProofSpaceTransitionWindows.sampled_threshold_by_initial_imbalance    (f : ℕ → ℤ) (block K : ℕ)
--       (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
--       (hsize : f 0 ≤ K) :
--       ∃ k ≤ K, IsFirstSampledThreshold f block k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProofSpaceTransitionWindows.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProofSpaceTransitionWindows.lean#L171

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

theorem ProofSpaceTransitionWindows.sampled_threshold_by_initial_imbalance    (f : ℕ → ℤ) (block K : ℕ)
    (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
    (hsize : f 0 ≤ K) :
    ∃ k ≤ K, IsFirstSampledThreshold f block k := by sorry
