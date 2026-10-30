-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:12:21.59746+00:00
-- url     : https://prove2.me/theorems/e73ff22e-f70f-4660-a70a-0473b483cc4f
-- title:
--   Truncated rescaled saddle integrands
-- statement:
--   Hfun evaluates the normalized saddle integrand at angle x/sqrt(B_n) inside the window |x|≤delta_n sqrt(B_n), and is zero outside. This is the actual truncated function used for Gaussian dominated-convergence estimates.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/GaussianCore.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Gaussian central saddle core

This file packages the reusable dominated-convergence core for the central
Gaussian window after the saddle scaling `theta = x / sqrt (B n)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The scaled central integrand with the moving cutoff built in. -/
def Hfun (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  if |x| ≤ δ n * Real.sqrt (B n) then
    saddleG f r n (x / Real.sqrt (B n))
  else
    0

/-
Note: the prompt-shaped version dropping the measurability hypothesis is omitted;
Mathlib's dominated convergence genuinely requires `AEStronglyMeasurable` of the
integrands, which is not implied by pointwise convergence + domination for an
arbitrary `f`. The clean theorem `central_tendsto_one_of_dominated_of_aestronglyMeasurable`
takes it as a hypothesis (discharged easily for continuous integrands, e.g. the exp testbed).
-/


