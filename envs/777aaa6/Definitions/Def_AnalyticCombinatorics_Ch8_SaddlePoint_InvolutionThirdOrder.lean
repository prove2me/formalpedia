-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T22:59:50.109229+00:00
-- url     : https://prove2.me/theorems/6b674ddf-da9c-40f1-a7f0-7449d04b65a9
-- title:
--   Higher quadratic saddle polynomials and shared correction scale
-- statement:
--   For real \(r\), `involSaddleB5Real r` and `involSaddleB6Real r` are the polynomials \(r+16r^2\) and \(r+32r^2\). The third definition is the literal alias
--   ```lean
--   def involThirdCorrScale (r : ℝ) : ℝ :=
--     involSecondCorrScale r
--   ```
--   Thus this bundle uses the same correction-scale function already named `involSecondCorrScale`.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
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
# Third-order saddle data for involutions

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2)`.  The fifth and sixth logarithmic saddle derivatives are
`b₅(r)=r+16r²` and `b₆(r)=r+32r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

noncomputable section

namespace InvolutionHAdmissible

/-- Fifth logarithmic saddle derivative for involutions. -/
def involSaddleB5Real (r : ℝ) : ℝ :=
  r + 16 * r ^ 2

/-- Sixth logarithmic saddle derivative for involutions. -/
def involSaddleB6Real (r : ℝ) : ℝ :=
  r + 32 * r ^ 2

/--
Robust third-order scale used by the current `ThirdOrderHAdmissible` interface.
The abstract wrapper requires this scale to dominate the second-order absolute
coefficient scale, so for involutions the existing second-order scale is the
natural reusable choice.
-/
def involThirdCorrScale (r : ℝ) : ℝ :=
  involSecondCorrScale r

end InvolutionHAdmissible


