-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CayleySecondOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CayleySecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:00.853993+00:00
-- url     : https://prove2.me/theorems/1634d96c-7da2-4740-a4be-32abe15e4acd
-- title:
--   Second Cayley correction and logarithmic Stirling auxiliaries
-- statement:
--   The leading coefficient scale is exp(n)/(sqrt(2pi)n^(3/2)); the second relative correction is -1/(12n). Private logarithmic Stirling-sequence functions record the log value, its centered tail and its reciprocal-index correction.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CayleySecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# Second-order Cayley tree-function coefficient asymptotic

This file proves the second relative coefficient for

`treeFunctionCoeff n = n^(n-1) / n!`.

The proof uses Stirling's sequence.  Robbins' stepwise upper bound and the
first positive term in Mathlib's exact series for
`log (stirlingSeq n) - log (stirlingSeq (n+1))` squeeze

`log (stirlingSeq n / sqrt pi) = 1/(12n) + o(1/n)`.

Exponentiating and inverting gives the Cayley correction `c = -1/12`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

noncomputable section

def cayleyRelativeSecondConstant : ℝ :=
  -(1 / 12 : ℝ)

def cayleyMainTerm (n : ℕ) : ℝ :=
  Real.exp (n : ℝ) /
    (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))

def cayleySecondOrderApprox (n : ℕ) : ℝ :=
  cayleyMainTerm n * (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹)

private def stirlingLog (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n)

private def stirlingLogTail (n : ℕ) : ℝ :=
  stirlingLog n - Real.log (Real.sqrt Real.pi)

private def stirlingLogCorr (n : ℕ) : ℝ :=
  (1 / 12 : ℝ) * (n : ℝ)⁻¹

end

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS


