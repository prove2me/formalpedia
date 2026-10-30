-- Prove2me | Theorems.Thm_FragmentedPermHAdmissible_fragPerm_count_over_factorial_thirdOrder
-- name    : FragmentedPermHAdmissible.fragPerm_count_over_factorial_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:56:52.862999+00:00
-- url     : https://prove2.me/theorems/6e7624a7-9d81-4c0d-a300-2e5f97c69b48
-- title:
--   Corrected saddle coefficients of the fragmented-permutation formal series
-- statement:
--   Let $a_n=[z^n]\exp(z/(1-z))$ be the literal source formal-series coefficient, $S_n=\texttt{fragPermThirdOrderSaddleScale}(n)$, and $r_n=\texttt{fragPermSaddleRadius}(n)$. With the two source corrections $c_2,c_3$ defined below, $$\frac{a_n}{S_n}-\bigl(1+c_2(n)+c_3(n)\bigr)=o\bigl(Q_2(r_n)\bigr),$$ where `fragPermThirdRobustCorrScale = fragPermSecondCorrScale` and $Q_2$ denotes that second scale. The separate intermediate scale `(1-r)^2` is not substituted for the final robust scale. This theorem concerns formal coefficients; no new finite-object counting bridge is asserted.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def fragPermThirdCorrScale (r : ℝ) : ℝ :=
--     (1 - r) ^ 2
--   ```
--
--   ```lean
--   def fragPermThirdOrderSaddleScale (n : ℕ) : ℂ :=
--     saddleScale fragPermFun fragPermSaddleRadius
--       (fun n => fragPermSaddleBReal (fragPermSaddleRadius n)) n
--   ```
--
--   ```lean
--   def fragPermThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
--     saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
--       fragPermSaddleB5Real fragPermSaddleB6Real (fragPermSaddleRadius n)
--   ```
--
--   ```lean
--   def fragPermThirdRobustCorrScale (r : ℝ) : ℝ :=
--     fragPermSecondCorrScale r
--   ```
--
--   ```lean
--   def fragPermSaddleB5Real (r : ℝ) : ℝ :=
--     r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
--   ```
--
--   ```lean
--   def fragPermSaddleB6Real (r : ℝ) : ℝ :=
--     r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
--       (1 - r) ^ 7
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean#L4356. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open FragmentedPermHAdmissible

theorem FragmentedPermHAdmissible.fragPerm_count_over_factorial_thirdOrder :
    (fun n : ℕ =>
      fragPermSeries.coeff n / fragPermThirdOrderSaddleScale n -
        (1 + (fragPermSecondCorrectionAtSaddle n : ℂ) +
          (fragPermThirdCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (fragPermThirdRobustCorrScale (fragPermSaddleRadius n) : ℂ)) := by sorry
