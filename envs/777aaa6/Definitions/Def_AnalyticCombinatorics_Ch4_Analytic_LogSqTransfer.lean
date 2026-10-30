-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSqTransfer
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogSqTransfer
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:44:40.591023+00:00
-- url     : https://prove2.me/theorems/f37eada9-c122-4d8d-b0ba-b6356cd1b794
-- title:
--   Log Sq Transfer
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   noncomputable def logSqSingularityFun (α : ℂ) : ℂ → ℂ :=
--     fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogSqTransfer.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
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
# Squared-logarithm singularity transfer (strong-remainder form)

`(1-z)^{-α}·log²(1/(1-z))` with strong residual `o(|1-z|^{-α})` ⟹
`[zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)²`.

The model coefficient identity is `coeff_logSqGF_eq_logSqSingularityCoeffℂ` (LogSqCoeff) and the
real asymptotic is `logSqSingularityScale_isEquivalent` (LogSqSingularity).  As in the one-log
strong-remainder transfer, the residual error `o(n^{α-1})` from the algebraic Darboux descent is
absorbed into `o(n^{α-1}(log n)²)` — no new contour estimate.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The squared-logarithm model function. -/
noncomputable def logSqSingularityFun (α : ℂ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ 2


