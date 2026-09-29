-- Prove2me | Theorems.Thm_FiniteRateDistortion_neg_div_exp_one_le_mul_log_div
-- name    : FiniteRateDistortion.neg_div_exp_one_le_mul_log_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:47:29.56033+00:00
-- url     : https://prove2.me/theorems/f411a975-01f8-407e-8283-1c0f723c7954
-- title:
--   `w · log (w / q) ≥ -q/e` for nonnegative `w, q` (with Lean's junk conventions at
-- statement:
--   `w · log (w / q) ≥ -q/e` for nonnegative `w, q` (with Lean's junk conventions at
--   `0`).  This is what keeps the information functional bounded below.
--
--   ```lean
--   theorem FiniteRateDistortion.neg_div_exp_one_le_mul_log_div{w q : ℝ} (hw : 0 ≤ w) (hq : 0 ≤ q) :
--       -(q / Real.exp 1) ≤ w * Real.log (w / q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FiniteRateDistortion/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FiniteRateDistortion/Core.lean#L82

-- Thm stub generated from Bridges/FiniteRateDistortion/Core.lean
import Mathlib
import Definitions.Def_Bridges_FiniteRateDistortion_Core

/-!
# Finite rate–distortion theory: channels, mutual information, and the Lagrangian dual

This module supplies the objects used by
`Bridges/FiniteRateDistortion/TropicalEnvelope.lean`, which referred to a finite
rate-distortion vocabulary that no module in the catalog provided.

Everything is finite and elementary:

* `FinProbDist α`, `Channel α β` — a source distribution and a test channel;
* `mutualInfo`, `distortion` — the two functionals of a channel;
* `rateDistortion μ d D` — the infimum of the mutual information over channels meeting
  the distortion constraint;
* `lagrangianDual μ d s` — the infimum of `I(W) + s · d(W)`;
* `lagrangianDual_le_rateDistortion` — **weak duality**: `Φ(s) - s·D ≤ R(D)` for every
  slope `s ≥ 0`, the affine lower bound whose tropical envelope is studied downstream.

The only analytic input is the elementary estimate `w · log (w / q) ≥ -q/e`
(`neg_div_exp_one_le_mul_log_div`), which makes the Lagrangian set bounded below, so the
infima are genuine.
-/

open Finset

noncomputable section

open FiniteRateDistortion

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## Sources and channels -/







/-! ## The elementary entropy estimate -/

theorem FiniteRateDistortion.neg_div_exp_one_le_mul_log_div{w q : ℝ} (hw : 0 ≤ w) (hq : 0 ≤ q) :
    -(q / Real.exp 1) ≤ w * Real.log (w / q) := by sorry
