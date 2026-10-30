-- Prove2me | Theorems.Thm_FragmentedPermHAdmissible_fragPerm_third_local_integrand_bound
-- name    : FragmentedPermHAdmissible.fragPerm_third_local_integrand_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:33:42.843751+00:00
-- url     : https://prove2.me/theorems/8d52b8b1-07c2-4bc8-9443-b4dc90022388
-- title:
--   Supporting lemma: fragPerm third local integrand bound
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   set_option backward.isDefEq.respectTransparency false in
--   private lemma fragPerm_third_local_integrand_bound {r x : ℝ}
--       (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
--       (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
--       (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
--       (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4)
--       (hWnorm :
--         ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
--       ‖Complex.exp (-(x ^ 2) / 2) *
--           (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
--               (x / Real.sqrt (fragPermSaddleBReal r)) -
--             saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
--               fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
--         ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
--             fragPermThirdLocalDom x
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermThirdOrder.lean#L4366. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder_x1
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
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

theorem FragmentedPermHAdmissible.fragPerm_third_local_integrand_bound {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4)
    (hWnorm :
      ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
      ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
          fragPermThirdLocalDom x := by sorry
