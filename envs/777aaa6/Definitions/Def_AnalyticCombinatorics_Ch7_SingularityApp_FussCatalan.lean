-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalan
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_FussCatalan
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:44:11.252093+00:00
-- url     : https://prove2.me/theorems/b7a6c340-39e0-49ba-820f-38a70282186a
-- title:
--   Fixed-arity Fuss–Catalan binomial sequences
-- statement:
--   The natural coefficient is Nat.choose(pn,n)/((p-1)n+1). The exponential base is p^p/(p-1)^(p-1), the leading coefficient constant is sqrt(p)/((p-1)^(3/2)sqrt(2pi)), and a related binomial scale retains its n^(-1/2) normalization. Natural-division and casting bridges are separate proved identities.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/FussCatalan.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# General Fuss-Catalan asymptotic

For fixed `p ≥ 2`, this file derives the Fuss-Catalan asymptotic
from Stirling's formula:

`1 / ((p - 1)n + 1) * choose (pn) n`
is equivalent to
`C_p * r_p^n * n^(-3/2)`, with
`r_p = p^p / (p - 1)^(p - 1)` and
`C_p = sqrt p / ((p - 1)^(3/2) sqrt (2π))`.
-/

open Filter Asymptotics
open scoped Topology

/-- The Fuss-Catalan number counting full `p`-ary trees with `n` internal nodes. -/
def fussCatalan (p n : ℕ) : ℕ :=
  Nat.choose (p * n) n / ((p - 1) * n + 1)

/-- The exponential growth base produced by Stirling's formula. -/
noncomputable def fussCatalanBase (p : ℕ) : ℝ :=
  (p : ℝ) ^ p / (((p - 1 : ℕ) : ℝ) ^ (p - 1))

/-- The simplified leading constant produced by Stirling's formula. -/
noncomputable def fussCatalanConst (p : ℕ) : ℝ :=
  Real.sqrt (p : ℝ) /
    ((((p - 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (2 * Real.pi))

noncomputable def fussCatalanChooseScale (p n : ℕ) : ℝ :=
  fussCatalanBase p ^ n * Real.sqrt (p : ℝ) /
    (Real.sqrt (((p - 1 : ℕ) : ℝ)) * Real.sqrt (2 * Real.pi * (n : ℝ)))


