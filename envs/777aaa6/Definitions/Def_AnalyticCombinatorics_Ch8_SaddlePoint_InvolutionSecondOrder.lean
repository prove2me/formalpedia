-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T22:57:58.498353+00:00
-- url     : https://prove2.me/theorems/0e73c130-49e7-42b0-8263-3486169e5751
-- title:
--   Quadratic saddle correction data and complex coefficient scale
-- statement:
--   For real \(r\), this bundle defines \(B_3(r)=r+4r^2\) and \(B_4(r)=r+8r^2\) as `involSaddleB3Real` and `involSaddleB4Real`. With \(B(r)=r+2r^2\), `involSecondCorrScale r` is the existing absolute correction-scale expression
--   \[
--   \frac{|B_4(r)|}{B(r)^2}+\frac{B_3(r)^2}{B(r)^3}.
--   \]
--   For natural \(n\), `involSecondOrderSaddleScale n` applies the existing complex `saddleScale` to \(F(z)=\exp(z+z^2/2)\), the radius sequence \(r_n=(\sqrt{1+4n}-1)/2\), and the sequence \(B(r_n)\). The fifth definition, `involCoeffC n`, is the complex cast of `involCoeffR n`.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
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
# Second-order saddle data for involutions

This file adds the second-order correction layer for
`exp (z + z^2 / 2)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²` and `b₄(r)=r+8r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace InvolutionHAdmissible

/-- Third logarithmic saddle derivative for involutions. -/
def involSaddleB3Real (r : ℝ) : ℝ :=
  r + 4 * r ^ 2

/-- Fourth logarithmic saddle derivative for involutions. -/
def involSaddleB4Real (r : ℝ) : ℝ :=
  r + 8 * r ^ 2

/-- Robust second-order correction scale for involutions. -/
def involSecondCorrScale (r : ℝ) : ℝ :=
  saddleCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real r

/-- Complex saddle scale used by the involution second-order statement. -/
def involSecondOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale involFun involSaddleRadius
    (fun n => involSaddleBReal (involSaddleRadius n)) n

/-- The EGF coefficient `I_n/n!` as a complex number. -/
def involCoeffC (n : ℕ) : ℂ :=
  (involCoeffR n : ℂ)

end InvolutionHAdmissible


