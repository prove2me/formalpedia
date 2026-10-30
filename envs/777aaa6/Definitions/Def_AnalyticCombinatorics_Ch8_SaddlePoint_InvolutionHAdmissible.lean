-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T22:54:40.893869+00:00
-- url     : https://prove2.me/theorems/3a88d810-c6a2-413b-8a36-7487b8fa27d6
-- title:
--   Size-one-or-two block coefficients and quadratic saddle data
-- statement:
--   For \(n\in\mathbb N\), `involCoeffR n` is the real number \(\texttt{parts12.set.counts}(n)/n!\). The source labelled-set model consists of finite partitions of the labels, with a `parts12` structure on each block; `parts12` has one structure at size one and one at size two. This bundle also defines the complex function \(F(z)=\exp(z+z^2/2)\) as `involFun`, the real polynomial \(B(r)=r+2r^2\) as `involSaddleBReal`, and \(r_n=(\sqrt{1+4n}-1)/2\) as `involSaddleRadius n`.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
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
# Involution H-admissible saddle data

This file records the Hayman data for the involution EGF
`exp (z + z^2 / 2)`.  The saddle data are
`a(r)=r+r^2`, `b(r)=r+2r^2`, and `δ(r)=r^(-3/4)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace InvolutionHAdmissible

abbrev involCoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) / n.factorial

/-- The analytic function `exp (z + z^2/2)`. -/
abbrev involFun (z : ℂ) : ℂ :=
  Complex.exp (z + z ^ 2 / 2)

/-- Continuous involution saddle variance scale, `b(r)=r+2r^2`. -/
def involSaddleBReal (r : ℝ) : ℝ :=
  r + 2 * r ^ 2

/-- The nonnegative saddle radius solving `r^2+r=n`. -/
def involSaddleRadius (n : ℕ) : ℝ :=
  (Real.sqrt (1 + 4 * (n : ℝ)) - 1) / 2

end InvolutionHAdmissible


