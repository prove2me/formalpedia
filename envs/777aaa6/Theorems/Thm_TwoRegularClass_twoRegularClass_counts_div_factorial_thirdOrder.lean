-- Prove2me | Theorems.Thm_TwoRegularClass_twoRegularClass_counts_div_factorial_thirdOrder
-- name    : TwoRegularClass.twoRegularClass_counts_div_factorial_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:19:19.459572+00:00
-- url     : https://prove2.me/theorems/2bce1537-076d-4713-ac9f-0e81fa20f1e0
-- title:
--   Three factorial-normalized terms for a set of unoriented cycles
-- statement:
--   Let $\mathcal U$ consist of single-cycle permutations on at least three labels modulo reversal, and let $\mathcal A=\operatorname{SET}(\mathcal U)$ be the source labelled set class. Put $A=e^{-3/4}/\sqrt\pi$. Then $$\frac{|\mathcal A_n|}{n!}-A\left(n^{-1/2}-\frac58n^{-3/2}+\frac1{128}n^{-5/2}\right)=o(n^{-5/2}).$$ These are the source cycle-quotient/set objects; no SimpleGraph degree-two equivalence is supplied by this theorem.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TwoRegularThirdOrder.lean#L536. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegular
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order asymptotics for 2-regular labelled graphs

This file proves the three-term singularity-analysis expansion for

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

open TwoRegularClass

theorem TwoRegularClass.twoRegularClass_counts_div_factorial_thirdOrder :
    (fun n : ℕ =>
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by sorry
