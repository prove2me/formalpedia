-- Prove2me | Theorems.Thm_catalan_isTheta
-- name    : catalan_isTheta
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:34:08.768752+00:00
-- url     : https://prove2.me/theorems/4287fd8d-6b50-41ac-b5ea-25c24b517f14
-- title:
--   Two-sided Catalan growth order
-- statement:
--   For the source Catalan number sequence, $$\operatorname{Catalan}_n=\Theta\!\left(\frac{4^n}{\sqrt\pi\,n^{3/2}}\right)\qquad(n\to\infty).$$ This conclusion is two-sided asymptotic order.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/GrowthRates.lean#L20. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
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
# Growth-rate corollaries of exact asymptotics

This file records API-level growth-rate consequences derived from the existing
asymptotic-equivalent headlines.
-/

open Filter Asymptotics
open scoped Topology BigOperators

theorem catalan_isTheta :
    (fun n : ℕ => (catalan n : ℝ)) =Θ[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by sorry
