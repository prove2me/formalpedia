-- Prove2me | Theorems.Thm_riordan_thirdOrder
-- name    : riordan_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:31:15.17364+00:00
-- url     : https://prove2.me/theorems/96713ba1-348a-4db7-beef-a09a558a48bf
-- title:
--   Riordan third-order sequence expansion
-- statement:
--   For the literal source recursively defined riordan sequence $m_n$, let $A=3\sqrt3/(8\sqrt\pi)$. Then $$m_n-3^n A n^{-3/2}\left(1+(-21/16)n^{-1}+(685/512)n^{-2}\right)=o(3^n n^{-7/2}).$$ The numeric source sequence is retained; no additional path-datatype identification is assumed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/RiordanThirdOrder.lean#L795. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RiordanSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RiordanThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Riordan
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order Riordan asymptotics

This file plugs the Riordan square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

theorem riordan_thirdOrder :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n * riordanAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + riordanRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ)) +
            riordanRelativeThirdConstant * (n : ℝ) ^ (-(2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by sorry
