-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_SchroederThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:29:47.632791+00:00
-- url     : https://prove2.me/theorems/0be56cb5-f40d-4185-b505-eeb9bb34a3c5
-- title:
--   Complex third-order large-Schröder expansion
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def schroederThirdLeadingConstantℂ : ℂ :=
--     sqrtSingularityC0 schroederSingularCoeff
--   ```
--
--   ```lean
--   def schroederRelativeSecondMetaConstantℂ : ℂ :=
--     sqrtSingularityC1 schroederRho schroederSingularCoeff schroederSingularDerivAtRho /
--       schroederThirdLeadingConstantℂ
--   ```
--
--   ```lean
--   def schroederRelativeThirdMetaConstantℂ : ℂ :=
--     sqrtSingularityC2 schroederRho schroederSingularCoeff schroederSingularDerivAtRho
--         schroederSingularSecondDerivAtRho /
--       schroederThirdLeadingConstantℂ
--   ```
--
--   ```lean
--   def schroederSingularDerivAtRho : ℂ :=
--     -schroederSecondSingularCoeff / schroederRhoℂ
--   ```
--
--   ```lean
--   def schroederSingularSecondDerivAtRho : ℂ :=
--     2 * schroederThirdSingularCoeff / schroederRhoℂ ^ 2
--   ```
--
--   ```lean
--   def schroederThirdSingularCoeff : ℂ :=
--     -2 * schroederThirdKℂ / schroederOneSubRhoℂ ^ 2
--   ```
--
--   ```lean
--   def schroederThirdKℂ : ℂ :=
--     schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
--       schroederSqrtRegularQuadraticCoeff
--   ```
--
--   ```lean
--   def schroederSqrtRegularLinearCoeff : ℂ :=
--     schroederRhoℂ ^ 2 / (2 * schroederSqrtRegularAtOneℂ)
--   ```
--
--   ```lean
--   def schroederSqrtRegularQuadraticCoeff : ℂ :=
--     -(schroederRhoℂ ^ 4) / (8 * schroederSqrtRegularAtOneℂ ^ 3)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/SchroederThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularitySecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SqrtSingularityThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Schroeder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_SchroederSecondOrder
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
# Third-order large Schroeder asymptotics

This file plugs the large-Schroeder square-root data at
`ρ = 3 - 2 * sqrt 2` into the third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def schroederSqrtRegularLinearCoeff : ℂ :=
  schroederRhoℂ ^ 2 / (2 * schroederSqrtRegularAtOneℂ)

def schroederSqrtRegularQuadraticCoeff : ℂ :=
  -(schroederRhoℂ ^ 4) / (8 * schroederSqrtRegularAtOneℂ ^ 3)

def schroederThirdKℂ : ℂ :=
  schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
    schroederSqrtRegularQuadraticCoeff

def schroederThirdSingularCoeff : ℂ :=
  -2 * schroederThirdKℂ / schroederOneSubRhoℂ ^ 2

def schroederSingularDerivAtRho : ℂ :=
  -schroederSecondSingularCoeff / schroederRhoℂ

def schroederSingularSecondDerivAtRho : ℂ :=
  2 * schroederThirdSingularCoeff / schroederRhoℂ ^ 2

def schroederThirdLeadingConstantℂ : ℂ :=
  sqrtSingularityC0 schroederSingularCoeff

def schroederRelativeSecondMetaConstantℂ : ℂ :=
  sqrtSingularityC1 schroederRho schroederSingularCoeff schroederSingularDerivAtRho /
    schroederThirdLeadingConstantℂ

def schroederRelativeThirdMetaConstantℂ : ℂ :=
  sqrtSingularityC2 schroederRho schroederSingularCoeff schroederSingularDerivAtRho
      schroederSingularSecondDerivAtRho /
    schroederThirdLeadingConstantℂ


