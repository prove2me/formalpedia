-- Prove2me | Theorems.Thm_ternaryTreeCount_normalized_thirdOrder
-- name    : ternaryTreeCount_normalized_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:40:01.190715+00:00
-- url     : https://prove2.me/theorems/721ed6eb-d9c6-45ad-a78f-ee00f5bf96c5
-- title:
--   Normalized ternary-tree sequence expansion with an inverse-cube bound
-- statement:
--   Let $t_n$ be the source ternary Fuss–Catalan sequence and $A=\sqrt3/(4\sqrt\pi)$. Then $$\frac{t_n}{(27/4)^nA n^{-3/2}}-\left(1-\frac{43}{72n}+\frac{3145}{10368n^2}\right)=O(n^{-3}).$$ This is the source unconditional numeric normalized result with Big-O inverse-cube error. It carries no analytic function or dented-domain premise.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryTreeThirdOrder.lean#L490. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order ternary-tree asymptotics

This file records the ternary-tree square-root data at `ρ = 4 / 27` and plugs
it into the committed third-order square-root applicator.  The unconditional
Gamma-ratio check at the end gives the same relative coefficient.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

theorem ternaryTreeCount_normalized_thirdOrder :
    (fun n : ℕ =>
      (ternaryTreeCount n : ℝ) /
          ((27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by sorry
