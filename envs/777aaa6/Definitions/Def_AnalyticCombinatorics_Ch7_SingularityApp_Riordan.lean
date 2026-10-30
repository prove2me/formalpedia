-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Riordan
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_Riordan
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:26:05.545325+00:00
-- url     : https://prove2.me/theorems/02dd16bf-1fe9-4ed9-baf9-61efb56f5b42
-- title:
--   Riordan
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def riordan : ℕ → ℕ
--     | 0 => 1
--     | 1 => 0
--     | n + 2 => ∑ k : Fin (n + 1), motzkin k * riordan (n - k)
--   termination_by n => n
--   decreasing_by omega
--   ```
--
--   ```lean
--   def riordanAsymptoticConstant : ℝ :=
--     3 * Real.sqrt 3 / (8 * Real.sqrt Real.pi)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/Riordan.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Motzkin
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
# Riordan-number asymptotic

This file proves the square-root singularity asymptotic for the Riordan
numbers, using the first-return decomposition of Riordan paths:

`R(z) = 1 + z^2 M(z) R(z)`.

The explicit branch is

`R(z) = 2 / (1 + z + sqrt(1 - 2 z - 3 z^2))`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Riordan numbers: Motzkin paths with no horizontal step at height zero.
The recurrence is the first-return decomposition
`R = 1 + z^2 M R`. -/
def riordan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => ∑ k : Fin (n + 1), motzkin k * riordan (n - k)
termination_by n => n
decreasing_by omega

/-- The real transfer constant in the form `C * 3^n * n^(-3/2)`. -/
def riordanAsymptoticConstant : ℝ :=
  3 * Real.sqrt 3 / (8 * Real.sqrt Real.pi)


