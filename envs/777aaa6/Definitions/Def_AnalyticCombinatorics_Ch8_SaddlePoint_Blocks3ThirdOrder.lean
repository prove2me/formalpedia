-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3ThirdOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3ThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:47:45.704726+00:00
-- url     : https://prove2.me/theorems/55893bcd-a4ac-43da-a5b7-6c83fc9807d0
-- title:
--   Higher cubic saddle polynomials and the third-order coefficient error
-- statement:
--   For real \(r\), `blocks3SaddleB5Real r` and `blocks3SaddleB6Real r` are \(r+16r^2+81r^3/2\) and \(r+32r^2+243r^3/2\). The comparison scale is the literal alias
--   ```lean
--   def blocks3ThirdCorrScale (r : ℝ) : ℝ :=
--     blocks3SecondCorrScale r
--   ```
--   For natural \(n\), `blocks3ThirdCorrectionAtSaddle n` is the existing real `saddleThirdCorrection` with data \(B,B_3,B_4,B_5,B_6\) at \(r_n\), and `blocks3ThirdOrderNumberError n` is the complex number
--   \[
--   \frac{a_n}{\texttt{blocks3SecondOrderSaddleScale}(n)}-\bigl(1+c_2(n)+c_3(n)\bigr),
--   \]
--   where \(a_n=\texttt{blocks3.counts}(n)/n!\) and \(c_2,c_3\) are `blocks3SecondCorrectionAtSaddle` and `blocks3ThirdCorrectionAtSaddle`.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Blocks3ThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3SecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order saddle data for blocks of size at most three

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2 + z^3 / 6)`.  The fifth and sixth logarithmic saddle
derivatives are
`b_5(r)=r+16r^2+81r^3/2` and `b_6(r)=r+32r^2+243r^3/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Blocks3HAdmissible

/-- Fifth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB5Real (r : ℝ) : ℝ :=
  r + 16 * r ^ 2 + 81 * r ^ 3 / 2

/-- Sixth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB6Real (r : ℝ) : ℝ :=
  r + 32 * r ^ 2 + 243 * r ^ 3 / 2

/--
Third-order scale required by the current abstract interface.  The interface's
`saddleThirdCorrectionScale` includes the second-order absolute coefficient
scale, so this reusable scale is the existing second-order one.
-/
def blocks3ThirdCorrScale (r : ℝ) : ℝ :=
  blocks3SecondCorrScale r

/-- The explicit third-order correction at the saddle radius. -/
def blocks3ThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleThirdCorrection blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
    blocks3SaddleB5Real blocks3SaddleB6Real (blocks3SaddleRadius n)

/-- Error term for `B_3(n) / n!` at third order. -/
def blocks3ThirdOrderNumberError (n : ℕ) : ℂ :=
  (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) /
      n.factorial : ℝ) : ℂ) /
    blocks3SecondOrderSaddleScale n -
      (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
        (blocks3ThirdCorrectionAtSaddle n : ℂ))

end Blocks3HAdmissible


