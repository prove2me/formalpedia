-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CatalanThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CatalanThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:45:39.170634+00:00
-- url     : https://prove2.me/theorems/f6fbccc2-715d-41b0-951d-be49c23aeee2
-- title:
--   Third Catalan correction and finite asymptotic models
-- statement:
--   The relative third Catalan coefficient is 145/128 and the absolute coefficient is 145/(128sqrt(pi)). Private central-binomial and Catalan models are explicit sums of three descending half-integer powers with their stated constants; they are approximation functions, not assumptions on the sequence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CatalanThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CatalanSecondOrder
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order Catalan asymptotics

This file proves the three-term Catalan asymptotic by combining the committed
third-order model coefficient estimate with the exact central-binomial bridge.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def catalanRelativeThirdConstant : ℝ :=
  145 / 128

def catalanThirdAsymptoticConstant : ℝ :=
  145 / (128 * Real.sqrt Real.pi)

def centralBinomSecondConstant : ℝ :=
  -(1 / (8 * Real.sqrt Real.pi))

def centralBinomThirdConstant : ℝ :=
  1 / (128 * Real.sqrt Real.pi)

def centralBinomThirdModel (n : ℕ) : ℝ :=
  catalanAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
    centralBinomSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
    centralBinomThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))

def catalanThirdModel (n : ℕ) : ℝ :=
  catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
    catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
    catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))

end


