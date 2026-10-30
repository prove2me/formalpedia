-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:08:57.816992+00:00
-- url     : https://prove2.me/theorems/c4937042-1684-44cf-a9bb-7877d4b44762
-- title:
--   Gaussian moment-generating function
-- statement:
--   The private auxiliary moment-generating function is exp(t²/2). It supplies the polynomial Gaussian moments through differentiation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/GaussianMoments.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Probability.Distributions.Gaussian.Real
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


set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Gaussian moments for the saddle correction

This file records the standard Gaussian moments needed by the second-order
saddle correction.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

def gaussianMGFCore (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2)


