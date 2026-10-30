-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:08:51.571299+00:00
-- url     : https://prove2.me/theorems/2df880c2-3750-47ac-801f-6c1137e36ad1
-- title:
--   Exponential saddle radii and Gaussian control
-- statement:
--   For exp(z), the radius and variance sequences are n, the window is n^(-2/5), and the scalar multilinear expansion is the exponential series. An explicit Gaussian dominator exp(-2x²/pi²) controls central rescaled integrands.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/ExpStirling.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
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
# The exponential saddle testbed

This file instantiates the saddle assembly machinery for `f z = exp z`.
The hard local-analysis estimates are isolated as explicitly documented
lemmas: the second-order exponential limit, the central domination estimate,
and the tail estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

def expSaddleRadius (n : ℕ) : ℝ := n

def expSaddleB (n : ℕ) : ℝ := n

def expSaddleDelta (n : ℕ) : ℝ := (n : ℝ) ^ (-(2 / 5 : ℝ))

noncomputable abbrev expSeriesC : FormalMultilinearSeries ℂ ℂ ℂ :=
  NormedSpace.expSeries ℂ ℂ

lemma exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp expSeriesC (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt expSeriesC.sum expSeriesC (0 : ℂ) := by
    exact (expSeriesC.hasFPowerSeriesOnBall
      (by
        rw [expSeriesC, NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : expSeriesC.sum = Complex.exp := by
    funext z
    calc
      expSeriesC.sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rwa [hfun] at hsum

def expCentralDominator (x : ℝ) : ℝ :=
  Real.exp (-(2 / Real.pi ^ 2) * x ^ 2)

end ExpStirling


