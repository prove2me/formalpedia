-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:12:34.239208+00:00
-- url     : https://prove2.me/theorems/15e82b58-6b1e-4af4-bae0-28ae7e1688cf
-- title:
--   Second saddle correction polynomial and robust scale
-- statement:
--   The polynomial P3 extends P2 through degree12 with explicit b3,b4,b5,b6 terms. Its integrated correction is d2 as displayed in the target metadata. For b>0, the robust absolute scale Q3 includes Q2 and the absolute sixth-derivative and mixed higher-order terms; it is not intrinsically a smaller scale. A private Gaussian moment-generating function supports its moments.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/ThirdOrderCore.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
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
# Third-order saddle core definitions

This file extends the universal second-order Gaussian correction polynomial by
the order-`b^{-2}` terms in the Hayman saddle expansion.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Third-order local polynomial in the scaled variable `x`. -/
def saddleThirdPoly (b b3 b4 b5 b6 : ℝ → ℝ) (r x : ℝ) : ℂ :=
  saddleSecondPoly b b3 b4 r x
    + Complex.I * ((b5 r : ℂ) / (120 * (Real.sqrt (b r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
    - ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) * (x : ℂ) ^ 6
    - Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
        (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 7
    + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) * (x : ℂ) ^ 8
    + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) * (x : ℂ) ^ 8
    + Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (b r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
    - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
        (x : ℂ) ^ 10)
    + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) * (x : ℂ) ^ 12

/-- The scalar third-order saddle correction `δ₂`. -/
def saddleThirdCorrection (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) : ℝ :=
  - b6 r / (48 * (b r) ^ 3)
    + 7 * b3 r * b5 r / (48 * (b r) ^ 4)
    + 35 * (b4 r) ^ 2 / (384 * (b r) ^ 4)
    - 35 * (b3 r) ^ 2 * b4 r / (64 * (b r) ^ 5)
    + 385 * (b3 r) ^ 4 / (1152 * (b r) ^ 6)

/--
Robust coefficient scale for the third-order polynomial.  It includes the
second-order coefficient scale because window truncation errors multiply every
nonconstant coefficient of the polynomial.
-/
def saddleThirdCorrectionScale (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) : ℝ :=
  saddleCorrectionScale b b3 b4 r
    + |b6 r| / (b r) ^ 3
    + |b3 r * b5 r| / (b r) ^ 4
    + (b4 r) ^ 2 / (b r) ^ 4
    + (b3 r) ^ 2 * |b4 r| / (b r) ^ 5
    + (b3 r) ^ 4 / (b r) ^ 6

@[simp] lemma saddleThirdPoly_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r x : ℝ) :
    saddleThirdPoly b b3 b4 b5 b6 r x =
      saddleSecondPoly b b3 b4 r x
        + Complex.I * ((b5 r : ℂ) / (120 * (Real.sqrt (b r) : ℂ) ^ 5)) *
            (x : ℂ) ^ 5
        - ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) * (x : ℂ) ^ 6
        - Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
            (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2)) *
            (x : ℂ) ^ 7
        + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
            (x : ℂ) ^ 8
        + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
            (x : ℂ) ^ 8
        + Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (b r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
        - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
            (x : ℂ) ^ 10)
        + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
            (x : ℂ) ^ 12 := rfl

@[simp] lemma saddleThirdCorrection_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    saddleThirdCorrection b b3 b4 b5 b6 r =
      - b6 r / (48 * (b r) ^ 3)
        + 7 * b3 r * b5 r / (48 * (b r) ^ 4)
        + 35 * (b4 r) ^ 2 / (384 * (b r) ^ 4)
        - 35 * (b3 r) ^ 2 * b4 r / (64 * (b r) ^ 5)
        + 385 * (b3 r) ^ 4 / (1152 * (b r) ^ 6) := rfl

@[simp] lemma saddleThirdCorrectionScale_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    saddleThirdCorrectionScale b b3 b4 b5 b6 r =
      saddleCorrectionScale b b3 b4 r
        + |b6 r| / (b r) ^ 3
        + |b3 r * b5 r| / (b r) ^ 4
        + (b4 r) ^ 2 / (b r) ^ 4
        + (b3 r) ^ 2 * |b4 r| / (b r) ^ 5
        + (b3 r) ^ 4 / (b r) ^ 6 := rfl

def gaussianMGFCoreThird (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2)


