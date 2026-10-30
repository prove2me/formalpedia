-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sq_drift_ge_onesided
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_ge_onesided
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:27:30.689545+00:00
-- url     : https://prove2.me/theorems/1778bedc-d09e-4e81-a46a-b33e797ff8ef
-- title:
--   A one-sided single-row quadratic-variation bound
-- statement:
--   Single-row mass, local variance and one-sided cross term only; there is no globally positive effective variance assumption. Identity kernel on a singleton, D=0,v0=eta=R=0 satisfies the listed premises.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma sq_drift_ge_onesided {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ) (v0 η R : ℝ) (x : ι)
--       (hKsum : ∑ z, K x z = 1) (hlvge : v0 ≤ locVar K D x)
--       (hcross : -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x)) :
--       v0 - 2 * R * η ≤ (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LocalizedQV.lean#L23. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_QVTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: one-sided (localized) lower quadratic variation

For the *conditioned* residual walk `K̂res`, the drift is NOT uniformly small: on-window it is a bounded
REPELLING drift (`D·e ≥ 0`), off-window it is the product drift (`|e| ≤ η`).  The energy/QV lower bound
needs only the ONE-SIDED bound `D x · (∑ K x z D z − D x) ≥ −R·η` (which holds in both regimes: off-window
`≥ −Rη`, on-window `≥ 0`), so the lower quadratic variation `E[D_T²] ≥ E[D_0²] + (v₀ − 2Rη)·T` survives
without uniform mart-eta.  This is the localization needed to apply the occupation argument to the
conditioned walk.  Deterministic finite-sum.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_ge_onesided {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ) (v0 η R : ℝ) (x : ι)
    (hKsum : ∑ z, K x z = 1) (hlvge : v0 ≤ locVar K D x)
    (hcross : -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x)) :
    v0 - 2 * R * η ≤ (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by sorry
