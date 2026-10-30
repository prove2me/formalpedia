-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffThirdOrder
-- name    : AnalyticCombinatorics_Ch4_Analytic_ModelCoeffThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:43:59.630276+00:00
-- url     : https://prove2.me/theorems/30b54550-d113-4233-9877-838b4873751d
-- title:
--   Third-order Gamma-ratio models
-- statement:
--   The normalized Gamma ratio and its one-step multiplier are paired with c1=alpha(alpha-1)/2 and c2=alpha(alpha-1)(alpha-2)(3alpha-1)/24. Private second- and third-order errors subtract the corresponding polynomial in 1/n; a further cubic coefficient supports the error analysis.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/ModelCoeffThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# Third-order model coefficient estimate

This file proves the third coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

def gammaRatioNorm (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) /
    ((n : ℝ) ^ (α - 1))

def gammaStep (α : ℝ) (n : ℕ) : ℝ :=
  (1 + α * (n : ℝ)⁻¹) * (1 + (n : ℝ)⁻¹) ^ (-α)

def c1 (α : ℝ) : ℝ :=
  α * (α - 1) / 2

def c2 (α : ℝ) : ℝ :=
  α * (α - 1) * (α - 2) * (3 * α - 1) / 24

def d3 (α : ℝ) : ℝ :=
  α * (α - 1) * (α + 1) / 3

def gammaSecondError (α : ℝ) (n : ℕ) : ℝ :=
  gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹

def gammaThirdError (α : ℝ) (n : ℕ) : ℝ :=
  gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹ -
    c2 α * ((n : ℝ)⁻¹) ^ 2


