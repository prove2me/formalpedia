-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:15.479163+00:00
-- url     : https://prove2.me/theorems/63c760b0-3fc6-4cb4-a049-d10be95335d1
-- title:
--   Ternary binomial sequence and Stirling scale
-- statement:
--   The natural sequence is Nat.choose(3n,n)/(2n+1), using natural division, and the real Stirling comparison scale is sqrt(2n*pi)(n/exp(1))^n. A tree datatype or cardinality equivalence is not introduced by these definitions.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryTrees.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
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
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

/-- The number of full ternary trees with `n` internal nodes. -/
def ternaryTreeCount (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n / (2 * n + 1)

noncomputable def stirlingScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.pi) * (((n : ℝ) / Real.exp 1) ^ n)


