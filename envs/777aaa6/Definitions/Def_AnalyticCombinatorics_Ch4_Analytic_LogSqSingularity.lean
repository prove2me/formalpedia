-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSqSingularity
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogSqSingularity
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:42:52.994988+00:00
-- url     : https://prove2.me/theorems/ddbbeb23-bd3d-4328-a88b-7fc1e82fbbd1
-- title:
--   Real squared-logarithmic coefficient scale
-- statement:
--   Real shifted finite sums of totalized inverse squares combine with the square of the shifted harmonic sum and a generalized binomial coefficient to define logSqSingularityScale. This expression is defined at every real parameter, including zero denominators; no unconditional equality with actual formal-series coefficients is included in the definition.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogSqSingularity.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib
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
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Coefficient scale for the squared-logarithm singularity `(1-z)^{-α} log²(1/(1-z))`

The `log²` model `(1-z)^{-α}·(-log(1-z))²` has `[zⁿ]` coefficient (morally `∂²_α` of the
binomial coefficient)

  `logSqSingularityScale α n := Ring.choose (α+n-1) n · ((shiftedHarmonic α n)² - shiftedHarmonic2 α n)`,

`shiftedHarmonic2 α n := ∑_{j<n} (α+j)⁻²`.  This file proves

  `logSqSingularityScale α n ~ n^{α-1}/Γ(α) · (log n)²`,

extending `logSingularityCoeff_isEquivalent`.  Since `0 ≤ shiftedHarmonic2 ≤ α⁻¹·shiftedHarmonic`
(termwise `(α+j)⁻² ≤ α⁻¹(α+j)⁻¹`), `shiftedHarmonic2 = O(log) = o(log²)`, so the bracket is
`~ (shiftedHarmonic)² ~ log²`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-- `∑_{j<n} (α+j)⁻²`, the second-order shifted harmonic sum. -/
def shiftedHarmonic2 (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((α + j) ^ 2)⁻¹

/-- The squared-logarithm coefficient scale. -/
def logSqSingularityScale (α : ℝ) (n : ℕ) : ℝ :=
  Ring.choose (α + n - 1) n * ((shiftedHarmonic α n) ^ 2 - shiftedHarmonic2 α n)


