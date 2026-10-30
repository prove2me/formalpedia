-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:08:36.172406+00:00
-- url     : https://prove2.me/theorems/67b2ad2b-4668-4dcb-99b4-28d2556b9d97
-- title:
--   First saddle correction polynomial and absolute scale
-- statement:
--   The complex polynomial P2 contains cubic imaginary, quartic and sextic terms. Gaussian integration gives d1=b4/(8b²)-5b3²/(24b³), while, for b>0, the nonnegative comparison expression is Q2=|b4|/b²+b3²/b³.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/SecondOrderCore.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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


/-!
# Second-order saddle core definitions

This file defines the universal Gaussian correction polynomial and the scalar
second-order correction appearing after integrating its even moments.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Second-order local polynomial in the scaled variable `x`. -/
def saddleSecondPoly (b b3 b4 : ℝ → ℝ) (r x : ℝ) : ℂ :=
  1
    - Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3)) * (x : ℂ) ^ 3
    + ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 4
    - (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3) * (x : ℂ) ^ 6

/-- The scalar second-order saddle correction. -/
def saddleCorrection (b b3 b4 : ℝ → ℝ) (r : ℝ) : ℝ :=
  b4 r / (8 * (b r) ^ 2) - 5 * (b3 r) ^ 2 / (24 * (b r) ^ 3)

/--
Robust absolute correction scale.  This is the scale used before specializing
to the signed correction, so cancellation in `saddleCorrection` does not hide
the true error size.
-/
def saddleCorrectionScale (b b3 b4 : ℝ → ℝ) (r : ℝ) : ℝ :=
  |b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3

@[simp] lemma saddleSecondPoly_apply (b b3 b4 : ℝ → ℝ) (r x : ℝ) :
    saddleSecondPoly b b3 b4 r x =
      1
        - Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3)) * (x : ℂ) ^ 3
        + ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 4
        - (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3) * (x : ℂ) ^ 6 := rfl

@[simp] lemma saddleCorrection_apply (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    saddleCorrection b b3 b4 r =
      b4 r / (8 * (b r) ^ 2) - 5 * (b3 r) ^ 2 / (24 * (b r) ^ 3) := rfl

@[simp] lemma saddleCorrectionScale_apply (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    saddleCorrectionScale b b3 b4 r =
      |b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3 := rfl


