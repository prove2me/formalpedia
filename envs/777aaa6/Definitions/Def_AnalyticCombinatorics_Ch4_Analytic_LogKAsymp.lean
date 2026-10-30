-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogKAsymp
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogKAsymp
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:28.39978+00:00
-- url     : https://prove2.me/theorems/c59b3bd3-93c7-447f-b20e-f722cb6741dd
-- title:
--   Real finite-sum scales for logarithmic powers
-- statement:
--   Real finite sums of totalized shifted reciprocal powers and products over k-element subsets define shiftedPowerSum and shiftedElemSymm. The bracket is k! times the elementary symmetric sum, and the full scale multiplies that bracket by the generalized binomial coefficient. These are total expressions on their stated domains; their asymptotic or coefficient identities require the hypotheses of separate theorems.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogKAsymp.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
# General log^k singularity scale: asymptotic layer

This file builds on `LogKCoeff.lean`.

It proves the real elementary-symmetric bracket asymptotic

  `k! · e_k((α+j)⁻¹, j<n) ~ (log n)^k`

and the resulting coefficient scale

  `k! · choose(α+n-1,n) · e_k ~ n^(α-1)/Γ(α) · (log n)^k`.
-/

open Filter Asymptotics
open scoped BigOperators Topology PowerSeries

noncomputable section

namespace AnalyticCombinatorics

/-- Shifted power sums:
`p_r(n) = ∑_{j<n} ((α+j)⁻¹)^r`. -/
def shiftedPowerSum (α : ℝ) (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((α + (j : ℝ))⁻¹) ^ r

/-- Elementary symmetric function in `{(α+j)⁻¹ | j < n}`. -/
def shiftedElemSymm (α : ℝ) (k n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range n).powersetCard k,
    ∏ j ∈ s, (α + (j : ℝ))⁻¹

/-- The normalized logarithmic bracket `k! · e_k`. -/
def logKBracket (α : ℝ) (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * shiftedElemSymm α k n

/-- Full real coefficient scale for `(1-z)^(-α)·(-log(1-z))^k`. -/
def logKSingularityScale (α : ℝ) (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * Ring.choose (α + n - 1) n * shiftedElemSymm α k n

/-! ## Newton identity -/

end AnalyticCombinatorics


