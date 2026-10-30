-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:43:58.062982+00:00
-- url     : https://prove2.me/theorems/0ba97610-333b-434d-8887-a577948cb278
-- title:
--   Motzkin numbers and rescaled analytic models
-- statement:
--   The natural Motzkin sequence is defined by its quadratic convolution recurrence, and its complex formal series is rescaled by 1/3. Square-root branches of 1-z and 1+z/3 give the explicit analytic denominator and the centered singularity model; the leading constant is 3sqrt(3)/(2sqrt(pi)). A scalar multilinear-series-to-power-series map retains its actual coefficients.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Motzkin.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
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
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Motzkin-number asymptotic

This file isolates the Motzkin recurrence and the constant produced by the
square-root singularity at `1 / 3`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Motzkin numbers, with `M 0 = 1` and
`M (n + 1) = M n + sum_{k < n} M k * M (n - 1 - k)`. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 => motzkin n + ∑ k : Fin n, motzkin k * motzkin (n - 1 - k)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self n
  · exact Nat.lt_succ_of_lt k.2
  · exact Nat.lt_succ_of_le
      ((Nat.sub_le (n - 1) k).trans (Nat.pred_le n))

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def motzkinSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (motzkin n : ℂ)

/-- The rescaled series `M(z / 3)`. -/
def motzkinRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((3 : ℂ)⁻¹) motzkinSeriesℂ

/-- The formal substitution variable `z / 3`. -/
def motzkinScaleX : PowerSeries ℂ :=
  PowerSeries.C ((3 : ℂ)⁻¹) * PowerSeries.X

/-- The singular coefficient of `M(z / 3)` at `z = 1`. -/
def motzkinSingularCoeff : ℂ := -((3 * Real.sqrt 3 : ℝ) : ℂ)

def motzkinSqrtPlus (z : ℂ) : ℂ :=
  (1 + z / 3) ^ (1 / 2 : ℂ)

def motzkinSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

def motzkinSqrtThreeℂ : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

/-- Denominator of the explicit rescaled Motzkin OGF. -/
def motzkinRescaledDenominator (z : ℂ) : ℂ :=
  1 - z / 3 + motzkinSqrtPlus z * motzkinSqrtOneSub z

/-- The explicit analytic branch of `M(z / 3)`. -/
def motzkinRescaledFun (z : ℂ) : ℂ :=
  2 / motzkinRescaledDenominator z

/-- The centered explicit branch, with the regular value at `z = 1` removed. -/
def motzkinCenteredRescaledFun (z : ℂ) : ℂ :=
  motzkinRescaledFun z - 3

def motzkinSingularityQuotientModel (z : ℂ) : ℂ :=
  (((-1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z) * motzkinSqrtOneSub z) +
      (3 * motzkinSqrtThreeℂ * (1 - z / 3) - 3 * motzkinSqrtPlus z)) /
    motzkinRescaledDenominator z

/-- The rescaled Motzkin series with its regular constant term at the dominant
singularity subtracted.  This is the series to which the square-root transfer is
applied. -/
def motzkinCenteredRescaledSeriesℂ : PowerSeries ℂ :=
  motzkinRescaledSeriesℂ - PowerSeries.C (3 : ℂ)

def powerSeriesOfFMLSℂ (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.coeff n

/-- The real transfer constant in the form `K * 3^n * n^(-3/2)`. -/
def motzkinAsymptoticConstant : ℝ :=
  3 * Real.sqrt 3 / (2 * Real.sqrt Real.pi)


