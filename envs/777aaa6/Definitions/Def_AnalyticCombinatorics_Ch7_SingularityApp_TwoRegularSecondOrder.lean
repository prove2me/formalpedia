-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularSecondOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:16:09.554238+00:00
-- url     : https://prove2.me/theorems/32119eec-3ab5-4df0-950d-7a0eb5e67c79
-- title:
--   Two Regular Second Order
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def twoRegularSecondConstant : ℝ :=
--     -(5 / 8 : ℝ) * twoRegularAsymptoticConstant
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TwoRegularSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegular
import Mathlib
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Second-order asymptotics for 2-regular labelled graphs

This file applies the `0 < α < 1` second-order transfer theorem to

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The second-order constant for 2-regular labelled graph counts. -/
def twoRegularSecondConstant : ℝ :=
  -(5 / 8 : ℝ) * twoRegularAsymptoticConstant

end


