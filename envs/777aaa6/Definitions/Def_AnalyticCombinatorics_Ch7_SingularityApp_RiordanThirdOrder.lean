-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RiordanThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_RiordanThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:22:50.372321+00:00
-- url     : https://prove2.me/theorems/fb880009-15e2-413f-8978-a1d442ba49aa
-- title:
--   Riordan third-order sequence expansion
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def riordanRelativeThirdConstant : ℝ := 685 / 512
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/RiordanThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# Third-order Riordan asymptotics

This file plugs the Riordan square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def riordanRelativeThirdConstant : ℝ := 685 / 512

end


