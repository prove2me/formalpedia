-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CayleyThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CayleyThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:45:16.48169+00:00
-- url     : https://prove2.me/theorems/c2777a01-004a-4e04-a55a-fc569b97b2df
-- title:
--   Third Cayley correction and Stirling tails
-- statement:
--   The third relative Cayley constant is 1/288, giving the leading scale times 1-1/(12n)+1/(288n^2). Private logarithmic Stirling tails and upper/lower correction functions support the remainder estimate.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CayleyThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CayleySecondOrder
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order Cayley tree-function coefficient asymptotic

This file extends the Stirling route from `CayleySecondOrder` by one relative
order.  The sharper log-tail squeeze is

`1/(12n) - 1/n^3 ≤ log (stirlingSeq n / sqrt pi) ≤ 1/(12n)`,

which is enough to exponentiate `-log (stirlingSeq n / sqrt pi)` through the
quadratic term.  The third relative Cayley coefficient is `1/288`.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

noncomputable section

def cayleyRelativeThirdConstant : ℝ :=
  1 / 288

def cayleyThirdOrderApprox (n : ℕ) : ℝ :=
  cayleyMainTerm n *
    (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
      cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2)

def stirlingLog (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n)

def stirlingLogTail (n : ℕ) : ℝ :=
  stirlingLog n - Real.log (Real.sqrt Real.pi)

def stirlingLogCorr (n : ℕ) : ℝ :=
  (1 / 12 : ℝ) * (n : ℝ)⁻¹

def stirlingLogCorrLower (n : ℕ) : ℝ :=
  stirlingLogCorr n - ((n : ℝ)⁻¹) ^ 3

end

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS


