-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegular
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TwoRegular
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:15:04.141279+00:00
-- url     : https://prove2.me/theorems/834690cb-032e-4f43-a595-9ce486bb8a3d
-- title:
--   Two Regular
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def twoRegularAsymptoticConstant : ℝ :=
--     Real.exp (-(3 / 4 : ℝ)) / Real.sqrt Real.pi
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TwoRegular.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Complex.Liouville
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
# Two-regular labelled graphs

This file records the singularity-analysis asymptotic for the EGF

`exp (-z/2 - z^2/4) / sqrt (1 - z)`.

The sequence is defined through this EGF: `twoRegularGraphCount n / n!` is the
real coefficient of the Taylor expansion at zero.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The real leading constant produced by transfer. -/
def twoRegularAsymptoticConstant : ℝ :=
  Real.exp (-(3 / 4 : ℝ)) / Real.sqrt Real.pi


