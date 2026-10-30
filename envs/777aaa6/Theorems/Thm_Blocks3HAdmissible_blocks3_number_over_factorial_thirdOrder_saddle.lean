-- Prove2me | Theorems.Thm_Blocks3HAdmissible_blocks3_number_over_factorial_thirdOrder_saddle
-- name    : Blocks3HAdmissible.blocks3_number_over_factorial_thirdOrder_saddle
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:49:39.641662+00:00
-- url     : https://prove2.me/theorems/61272caf-1f76-4a04-9e6e-33e96b04a356
-- title:
--   Two displayed corrections with the source robust blocks-three remainder
-- statement:
--   Let $a_n$ be the factorial-normalized count of the source class `CombClass.blocks3`, $S_n=\texttt{blocks3SecondOrderSaddleScale}(n)$, $r_n=\texttt{blocks3SaddleRadius}(n)$, and let $c_2(n),c_3(n)$ be the source second and third saddle corrections defined below. In complex coefficients, $$\frac{a_n}{S_n}-\bigl(1+c_2(n)+c_3(n)\bigr)=o\bigl(Q_2(r_n)\bigr).$$ Here $Q_2=\texttt{blocks3SecondCorrScale}$ and the literal definition is `blocks3ThirdCorrScale = blocks3SecondCorrScale`. The named third correction does not change this to a sharper third-order error.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def blocks3ThirdCorrScale (r : ℝ) : ℝ :=
--     blocks3SecondCorrScale r
--   ```
--
--   ```lean
--   def blocks3ThirdOrderNumberError (n : ℕ) : ℂ :=
--     (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) /
--         n.factorial : ℝ) : ℂ) /
--       blocks3SecondOrderSaddleScale n -
--         (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
--           (blocks3ThirdCorrectionAtSaddle n : ℂ))
--   ```
--
--   ```lean
--   def blocks3ThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
--     saddleThirdCorrection blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
--       blocks3SaddleB5Real blocks3SaddleB6Real (blocks3SaddleRadius n)
--   ```
--
--   ```lean
--   def blocks3SaddleB5Real (r : ℝ) : ℝ :=
--     r + 16 * r ^ 2 + 81 * r ^ 3 / 2
--   ```
--
--   ```lean
--   def blocks3SaddleB6Real (r : ℝ) : ℝ :=
--     r + 32 * r ^ 2 + 243 * r ^ 3 / 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Blocks3ThirdOrder.lean#L1247. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3SecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3ThirdOrder
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

open Blocks3HAdmissible

theorem Blocks3HAdmissible.blocks3_number_over_factorial_thirdOrder_saddle :
    (fun n : ℕ => blocks3ThirdOrderNumberError n)
      =o[atTop]
    (fun n : ℕ => (blocks3ThirdCorrScale (blocks3SaddleRadius n) : ℂ)) := by sorry
