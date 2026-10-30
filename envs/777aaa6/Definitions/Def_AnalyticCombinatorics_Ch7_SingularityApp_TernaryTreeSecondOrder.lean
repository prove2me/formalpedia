-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeSecondOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:37:34.123327+00:00
-- url     : https://prove2.me/theorems/5eb2eb4f-3374-4ecb-94ed-641475cd295b
-- title:
--   Ternary Tree Second Order
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def ternaryAsymptoticConstant : ℝ :=
--     Real.sqrt 3 / (4 * Real.sqrt Real.pi)
--   ```
--
--   ```lean
--   def ternaryRelativeSecondConstant : ℝ :=
--     -(43 / 72 : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryTreeSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib
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
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
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
# Second-order ternary-tree asymptotics

This file records the second-order constants for the Fuss-Catalan `p = 3`
ternary-tree numbers.  The correction is computed from the three positive
Gamma ratios obtained from the exact Fuss-Catalan closed form.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

def ternaryAsymptoticConstant : ℝ :=
  Real.sqrt 3 / (4 * Real.sqrt Real.pi)

def ternaryRelativeSecondConstant : ℝ :=
  -(43 / 72 : ℝ)

end


