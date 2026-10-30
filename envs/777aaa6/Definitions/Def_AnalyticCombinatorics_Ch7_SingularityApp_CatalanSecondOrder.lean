-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CatalanSecondOrder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_CatalanSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:21.187008+00:00
-- url     : https://prove2.me/theorems/51bac2a4-1fba-4529-aea7-4b8244c736c9
-- title:
--   Catalan series and second-order constants
-- statement:
--   The complex generating series has coefficients given by the natural Catalan numbers and is rescaled by 1/4. Its principal square-root analytic branch is 2/(1+sqrt(1-z)); adjusted series subtract regular terms. The leading and second constants are 1/sqrt(pi) and -9/(8sqrt(pi)), with relative second coefficient -9/8.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/CatalanSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Liouville
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Second-order Catalan asymptotics

This file applies the general second-order transfer theorem at `α = -1/2` to
the centered rescaled Catalan OGF

`2 / (1 + sqrt (1 - z)) - 2 - 2 * (1 - z)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def catalanAsymptoticConstant : ℝ :=
  1 / Real.sqrt Real.pi

def catalanRelativeSecondConstant : ℝ :=
  -(9 / 8 : ℝ)

def catalanSecondAsymptoticConstant : ℝ :=
  -(9 / (8 * Real.sqrt Real.pi) : ℝ)

def catalanSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (catalan n : ℂ)

def catalanRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((4 : ℂ)⁻¹) catalanSeriesℂ

def catalanScaleX : PowerSeries ℂ :=
  PowerSeries.C ((4 : ℂ)⁻¹) * PowerSeries.X

def catalanSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

def catalanRescaledFun (z : ℂ) : ℂ :=
  2 / (1 + catalanSqrtOneSub z)

def catalanOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

def catalanAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  catalanRescaledSeriesℂ - PowerSeries.C (2 : ℂ) -
    PowerSeries.C (2 : ℂ) * catalanOneSubSeriesℂ

def catalanAdjustedRescaledFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS catalanAdjustedRescaledSeriesℂ

def catalanAdjustedRescaledFun (z : ℂ) : ℂ :=
  catalanRescaledFun z - 2 - 2 * (1 - z)

end


