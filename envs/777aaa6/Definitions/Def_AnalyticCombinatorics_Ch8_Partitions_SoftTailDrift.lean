-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SoftTailDrift
-- name    : AnalyticCombinatorics_Ch8_Partitions_SoftTailDrift
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:58:52.164355+00:00
-- url     : https://prove2.me/theorems/cdccafad-423b-433e-96d9-ce9a5521a46d
-- title:
--   Soft Tail Drift
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SoftTailDrift.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)

/-- The per-step mass moving further than `b` in `D`-value. -/
def farMass (b : ℝ) (x : ι) : ℝ :=
  ∑ z, K x z * (if |D z - D x| ≤ b then (0 : ℝ) else 1)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


