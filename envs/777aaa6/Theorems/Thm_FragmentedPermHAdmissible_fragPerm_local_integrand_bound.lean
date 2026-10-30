-- Prove2me | Theorems.Thm_FragmentedPermHAdmissible_fragPerm_local_integrand_bound
-- name    : FragmentedPermHAdmissible.fragPerm_local_integrand_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:42:48.316337+00:00
-- url     : https://prove2.me/theorems/d6859e01-cc62-4c8b-b672-22b841f3c9b5
-- title:
--   Supporting lemma: fragPerm local integrand bound
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermSecondOrder.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma fragPerm_local_integrand_bound {r x : ℝ}
--       (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
--       (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r)
--       (hδle : fragPermSaddleDeltaReal r ≤ 1)
--       (hδu : fragPermSaddleDeltaReal r ≤ (1 - r) / 4)
--       (hWnorm : ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
--       ‖Complex.exp (-(x ^ 2) / 2) *
--           (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
--               (x / Real.sqrt (fragPermSaddleBReal r)) -
--             saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
--         ≤ fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) * fragPermGaussianDom x
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermSecondOrder.lean#L1427. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
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
# Second-order saddle data for fragmented permutations

This file adds the second-order correction layer for
`exp (z / (1 - z))`.  The logarithmic saddle derivatives are
`b₃(r) = r(1 + 4r + r²)/(1-r)^4` and
`b₄(r) = r(1 + 11r + 11r² + r³)/(1-r)^5`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

open FragmentedPermHAdmissible

theorem FragmentedPermHAdmissible.fragPerm_local_integrand_bound {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r)
    (hδle : fragPermSaddleDeltaReal r ≤ 1)
    (hδu : fragPermSaddleDeltaReal r ≤ (1 - r) / 4)
    (hWnorm : ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
      ≤ fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) * fragPermGaussianDom x := by sorry
