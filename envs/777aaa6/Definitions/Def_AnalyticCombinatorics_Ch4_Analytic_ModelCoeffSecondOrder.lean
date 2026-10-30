-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffSecondOrder
-- name    : AnalyticCombinatorics_Ch4_Analytic_ModelCoeffSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:43:59.745996+00:00
-- url     : https://prove2.me/theorems/6814ed11-e095-4d47-be47-a122f3c013fb
-- title:
--   Second-order Gamma-ratio models
-- statement:
--   Private auxiliary functions are the normalized Gamma ratio, its one-step multiplier, the correction alpha(alpha-1)/2, and the error after subtracting 1 and that correction divided by n.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/ModelCoeffSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Second-order model coefficient estimate

This file proves the second coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private def gammaRatioNorm (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) /
    ((n : ℝ) ^ (α - 1))

private def gammaStep (α : ℝ) (n : ℕ) : ℝ :=
  (1 + α * (n : ℝ)⁻¹) * (1 + (n : ℝ)⁻¹) ^ (-α)

private def c1 (α : ℝ) : ℝ :=
  α * (α - 1) / 2

private def gammaSecondError (α : ℝ) (n : ℕ) : ℝ :=
  gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹


