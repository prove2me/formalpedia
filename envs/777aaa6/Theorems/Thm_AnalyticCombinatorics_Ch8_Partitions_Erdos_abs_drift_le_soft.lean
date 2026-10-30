-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_abs_drift_le_soft
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_soft
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:02:16.090659+00:00
-- url     : https://prove2.me/theorems/089c447c-9f9b-4f53-b1d9-5de4db0691a3
-- title:
--   A drift bound retaining the far-mass loss
-- statement:
--   A one-step drift bound includes an explicit far-mass loss; summability/smallness of that tail over the required horizon remains an input.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem abs_drift_le_soft (b R : ℝ) (x : ι) (hbnn : 0 ≤ b)
--       (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1) (hR : ∀ z, |D z| ≤ R) :
--       (∑ z, K x z * |D z|) ≤ |D x| + b + 2 * R * farMass K D b x
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SoftTailDrift.lean#L38. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SoftTailDrift
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Soft-tail Tanaka drift bound

The banked `abs_drift_le` needs a *global* hard increment bound (`K x z ≠ 0 → |D z − D x| ≤ b`).
The Erdős predecessor kernel only has *soft* far tails: most mass moves by `≤ b`, but a small
`farMass` moves further (up to the range `2R`).  This lemma charges that far mass to an additive
error: the one-step `|D|`-drift is `≤ b + 2R·farMass`, where

  `farMass K D b x = ∑_z K x z · 1[|D z − D x| > b]`.

Telescoped, this turns the Tanaka occupation bound into
`window-occupation ≥ (E|D_T| − E|D_0| − ηT − 2R·∑_t farMass_t)/b`, so a per-step far mass summing to
`o(√T)` over the horizon leaves the `√T` Paley–Zygmund signal intact.  Deterministic finite-sum.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_soft (b R : ℝ) (x : ι) (hbnn : 0 ≤ b)
    (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1) (hR : ∀ z, |D z| ≤ R) :
    (∑ z, K x z * |D z|) ≤ |D x| + b + 2 * R * farMass K D b x := by sorry
