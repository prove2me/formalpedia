-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_Meromorphic_Secant_secantNumber_div_factorial_even_isEquivalent
-- name    : AnalyticCombinatorics.Ch5.Meromorphic.Secant.secantNumber_div_factorial_even_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T22:10:44.631522+00:00
-- url     : https://prove2.me/theorems/6094d1c4-3b52-4726-a14b-ee18166bcf67
-- title:
--   Even secant-number asymptotics
-- statement:
--   Let $E_n$ be the source secant coefficient sequence, defined through the formal secant series. As $k\to\infty$, $$\frac{E_{2k}}{(2k)!}\sim2\left(\frac2\pi\right)^{2k+1}.$$ Only the even subsequence is asserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Secant.lean#L578. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Secant
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch5
open AnalyticCombinatorics.Ch5.Meromorphic
open AnalyticCombinatorics.Ch5.Meromorphic.Secant

theorem AnalyticCombinatorics.Ch5.Meromorphic.Secant.secantNumber_div_factorial_even_isEquivalent :
    (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) := by sorry
