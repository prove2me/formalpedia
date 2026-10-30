-- Prove2me | Theorems.Thm_InvolutionHAdmissible_involution_count_over_factorial_thirdOrder
-- name    : InvolutionHAdmissible.involution_count_over_factorial_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T23:01:45.55578+00:00
-- url     : https://prove2.me/theorems/569401c4-a59a-4cdf-a9e2-fa81613ac43f
-- title:
--   Two displayed corrections for the source involution EGF model
-- statement:
--   Let $a_n=\texttt{involCoeffC}(n)$, $S_n=\texttt{involSecondOrderSaddleScale}(n)$ and $r_n=\texttt{involSaddleRadius}(n)$ for the source class `parts12.set`. With the source saddle corrections $c_2,c_3$ defined below, $$\frac{a_n}{S_n}-\bigl(1+c_2(n)+c_3(n)\bigr)=o\bigl(Q_2(r_n)\bigr).$$ The literal equality `involThirdCorrScale = involSecondCorrScale` specifies $Q_2$; no sharper remainder is claimed. The coefficients and both correction functions retain their source normalization.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def involSaddleB5Real (r : ℝ) : ℝ :=
--     r + 16 * r ^ 2
--   ```
--
--   ```lean
--   def involSaddleB6Real (r : ℝ) : ℝ :=
--     r + 32 * r ^ 2
--   ```
--
--   ```lean
--   def involThirdCorrScale (r : ℝ) : ℝ :=
--     involSecondCorrScale r
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/InvolutionThirdOrder.lean#L1142. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_SequenceInverse
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionRealSaddle
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
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

open InvolutionHAdmissible

theorem InvolutionHAdmissible.involution_count_over_factorial_thirdOrder :
    (fun n : ℕ =>
      involCoeffC n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) +
          (saddleThirdCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involThirdCorrScale (involSaddleRadius n) : ℂ)) := by sorry
