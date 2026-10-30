-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Schroeder
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_Schroeder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:24:19.717966+00:00
-- url     : https://prove2.me/theorems/995860d7-bf18-4efe-9e65-b88733140b4b
-- title:
--   Schroeder
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def schroeder : ℕ → ℕ
--     | 0 => 1
--     | n + 1 => schroeder n + ∑ k : Fin (n + 1), schroeder k * schroeder (n - k)
--   termination_by n => n
--   decreasing_by
--     · exact Nat.lt_succ_self n
--     · exact k.2
--     · exact Nat.lt_succ_of_le (Nat.sub_le n k)
--   ```
--
--   ```lean
--   def schroederRhoℂ : ℂ := ((schroederRho : ℝ) : ℂ)
--   ```
--
--   ```lean
--   def schroederRho : ℝ := 3 - 2 * Real.sqrt 2
--   ```
--
--   ```lean
--   def schroederSingularCoeff : ℂ :=
--     -2 * schroederSqrtRegularAtOneℂ / schroederOneSubRhoℂ ^ 2
--   ```
--
--   ```lean
--   def schroederOneSubRhoℂ : ℂ := (((1 - schroederRho : ℝ) : ℂ))
--   ```
--
--   ```lean
--   def schroederSqrtRegularAtOneℂ : ℂ :=
--     ((Real.sqrt (1 - schroederRho ^ 2) : ℝ) : ℂ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Schroeder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Large Schroeder-number asymptotic

This file proves the square-root singularity asymptotic for the large
Schroeder numbers with OGF
`S(z) = (1 - z - sqrt (1 - 6 z + z^2)) / (2 z)`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Large Schroeder numbers, with `S 0 = 1` and
`S (n + 1) = S n + sum_{k = 0}^n S k * S (n - k)`. -/
def schroeder : ℕ → ℕ
  | 0 => 1
  | n + 1 => schroeder n + ∑ k : Fin (n + 1), schroeder k * schroeder (n - k)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self n
  · exact k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le n k)

/-- Dominant singularity, the smaller root of `1 - 6 z + z^2`. -/
def schroederRho : ℝ := 3 - 2 * Real.sqrt 2

def schroederRhoℂ : ℂ := ((schroederRho : ℝ) : ℂ)

def schroederOneSubRhoℂ : ℂ := (((1 - schroederRho : ℝ) : ℂ))

def schroederSqrtRegularAtOneℂ : ℂ :=
  ((Real.sqrt (1 - schroederRho ^ 2) : ℝ) : ℂ)

/-- The singular coefficient of `S(rho z)` at `z = 1`. -/
def schroederSingularCoeff : ℂ :=
  -2 * schroederSqrtRegularAtOneℂ / schroederOneSubRhoℂ ^ 2


