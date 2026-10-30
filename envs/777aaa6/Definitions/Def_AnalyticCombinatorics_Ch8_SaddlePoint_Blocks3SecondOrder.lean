-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3SecondOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3SecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:46:35.051008+00:00
-- url     : https://prove2.me/theorems/43fa1aff-8c90-4e2e-a161-729e9177118f
-- title:
--   Cubic saddle correction data and complex coefficient scale
-- statement:
--   For real \(r\), this bundle defines \(B_3(r)=r+4r^2+9r^3/2\) and \(B_4(r)=r+8r^2+27r^3/2\) as `blocks3SaddleB3Real` and `blocks3SaddleB4Real`, and the comparison scale `blocks3SecondCorrScale r` \(=r^{-3}\) (a real power). For natural \(n\), `blocks3SecondOrderSaddleScale n` applies the existing complex `saddleScale` to \(F(z)=\exp(z+z^2/2+z^3/6)\), the radius sequence \(r_n\), and the sequence \(B(r_n)\); `blocks3SecondCorrectionAtSaddle n` is the existing real `saddleCorrection` with data \(B,B_3,B_4\) evaluated at \(r_n\).
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Blocks3SecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
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
# Second-order saddle data for blocks of size at most three

This file adds the second-order correction layer for
`exp (z + z^2 / 2 + z^3 / 6)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²+9r³/2` and `b₄(r)=r+8r²+27r³/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace Blocks3HAdmissible

/-- Third logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB3Real (r : ℝ) : ℝ :=
  r + 4 * r ^ 2 + 9 * r ^ 3 / 2

/-- Fourth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB4Real (r : ℝ) : ℝ :=
  r + 8 * r ^ 2 + 27 * r ^ 3 / 2

/-- A robust second-order comparison scale for the cubic saddle. -/
def blocks3SecondCorrScale (r : ℝ) : ℝ :=
  r ^ (-(3 : ℝ))

/-- Complex saddle scale used by the blocks-≤3 second-order statement. -/
def blocks3SecondOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale blocks3Fun blocks3SaddleRadius
    (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n

/-- The explicit second-order correction at the saddle radius. -/
def blocks3SecondCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleCorrection blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
    (blocks3SaddleRadius n)

end Blocks3HAdmissible


