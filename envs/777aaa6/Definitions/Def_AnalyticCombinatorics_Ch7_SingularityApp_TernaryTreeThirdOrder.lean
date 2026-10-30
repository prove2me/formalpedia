-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeThirdOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:38:55.255734+00:00
-- url     : https://prove2.me/theorems/31d55328-e74d-4dec-a44a-c62a40194f9d
-- title:
--   Normalized ternary-tree sequence expansion with an inverse-cube bound
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def ternaryRelativeThirdConstant : ℝ :=
--     3145 / 10368
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryTreeThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order ternary-tree asymptotics

This file records the ternary-tree square-root data at `ρ = 4 / 27` and plugs
it into the committed third-order square-root applicator.  The unconditional
Gamma-ratio check at the end gives the same relative coefficient.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def ternaryRelativeThirdConstant : ℝ :=
  3145 / 10368

end


