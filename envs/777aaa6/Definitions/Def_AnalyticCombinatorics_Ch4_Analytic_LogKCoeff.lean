-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogKCoeff
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogKCoeff
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:42:40.642106+00:00
-- url     : https://prove2.me/theorems/9a7937c4-22a7-48b4-93f6-609b04ece3d4
-- title:
--   Elementary symmetric logarithmic coefficients
-- statement:
--   For natural k and n, shiftedElemSymmℂ sums products of totalized shifted reciprocals over k-element subsets of {0,...,n-1}. Multiplication by k! and a generalized binomial coefficient defines logKCoeffℂ; logKGF recursively multiplies the binomial formal series by the logarithmic formal series. Equality between the finite expression and actual series coefficients is a separate theorem with its own hypotheses.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogKCoeff.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Finset.Powerset
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
# General logarithmic coefficient hierarchy: GF coefficient identity

This file is the coefficient-identity layer for

  `(1 - z)^(-α) · (-log (1 - z))^k`.

It contains only:

* the elementary-symmetric closed coefficient scale,
* the recursive formal GF `logKGF`,
* formal ODE recurrences,
* the closed-form recurrence,
* and the GF ↔ closed coefficient identity.

No asymptotics and no analytic faithfulness are included here.
-/

open scoped BigOperators PowerSeries

noncomputable section

namespace AnalyticCombinatorics

open PowerSeries

/-- Elementary symmetric function in the shifted reciprocals
`{(α+j)⁻¹ | j < n}`. -/
def shiftedElemSymmℂ (α : ℂ) (k n : ℕ) : ℂ :=
  ∑ s ∈ (Finset.range n).powersetCard k,
    ∏ j ∈ s, (α + (j : ℂ))⁻¹

/-- Closed coefficient scale for
`(1-z)^(-α) · (-log(1-z))^k`.

The factor `k!` is essential:
`2! e₂ = H² - H₂`, recovering the banked log² coefficient. -/
def logKCoeffℂ (α : ℂ) (k n : ℕ) : ℂ :=
  (k.factorial : ℂ) * binCoeffℂ α n * shiftedElemSymmℂ α k n

/-- Recursive formal GF for the `k`-th logarithmic singularity. -/
noncomputable def logKGF (α : ℂ) : ℕ → PowerSeries ℂ
  | 0 => oneSubCpowGF α
  | k + 1 => logKGF α k * logGF

/-! ## Coefficients of `(1 - X)·F'` -/

/-! ## Formal ODEs -/

/-! ## Elementary-symmetric insertion recurrence -/

/-! ## Closed-form coefficient recurrence -/

/-! ## GF coefficient identity -/

end AnalyticCombinatorics


