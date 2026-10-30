-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogKFaithful
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogKFaithful
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:41.647996+00:00
-- url     : https://prove2.me/theorems/52affbcd-1455-4cb4-9f13-c865381a838d
-- title:
--   Principal algebraic-logarithmic model function
-- statement:
--   For complex alpha and natural k the model is (1-z)^(-alpha)(-Log(1-z))^k, with principal complex branches.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogKFaithful.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Finset.Powerset
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
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
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Faithfulness and Δ-analyticity for the fixed `log^k` hierarchy

`logKGF α k` is the formal model for

`(1 - z)^(-α) * (-log (1 - z))^k`.

This file proves the analytic faithfulness layer by induction on `k`, reusing the same
Cauchy-product bridge used for the one-log and two-log models.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The fixed-`k` logarithmic singularity model
`(1 - z)^(-α) * (-log (1 - z))^k`. -/
noncomputable def logKSingularityFun (α : ℂ) (k : ℕ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ k


