-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSqCoeff
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogSqCoeff
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:42:38.708456+00:00
-- url     : https://prove2.me/theorems/8aefb200-00ad-437c-ac84-4c9f085a907d
-- title:
--   Squared-logarithmic coefficient model
-- statement:
--   Complex finite sums of totalized squared reciprocals combine as H²-H₂, multiplied by a generalized binomial coefficient, to define logSqSingularityCoeffℂ. Multiplication of the single-log formal series by the logarithmic formal series defines logSqGF. The finite expression alone asserts no coefficient identity at arbitrary parameters, including zero denominators.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogSqCoeff.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib
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
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Coefficient identity for the squared-logarithm singularity GF

`logSqGF α := logSingularityGF α * logGF` is the formal power series of
`(1-z)^{-α}·(-log(1-z))²`.  Its coefficient is the closed form (morally `∂²_α` of the
binomial coefficient)

  `coeff n (logSqGF α) = logSqSingularityCoeffℂ α n
     = binCoeffℂ α n · ((shiftedHarmonicℂ α n)² - shiftedHarmonic2ℂ α n)`.

Proof (recurrence matching, mirroring the first-log `convCoeff_succ`/`sum_partialFraction`):
the Cauchy-product coefficient `∑_{m<n} logSingularityCoeffℂ α m · (n-m)⁻¹` and the closed form
both satisfy `(n+1)x(n+1) = (α+n)x(n) + 2·logSingularityCoeffℂ α n` with `x 0 = 0`.
-/

open scoped BigOperators

noncomputable section

namespace AnalyticCombinatorics

/-- `∑_{j<n} (α+j)⁻²` (complex). -/
def shiftedHarmonic2ℂ (α : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, ((α + j)⁻¹) ^ 2

/-- Closed-form squared-log coefficient `binCoeffℂ α n · (H² - H₂)`. -/
def logSqSingularityCoeffℂ (α : ℂ) (n : ℕ) : ℂ :=
  binCoeffℂ α n * ((shiftedHarmonicℂ α n) ^ 2 - shiftedHarmonic2ℂ α n)

/-- The squared-log generating function. -/
noncomputable def logSqGF (α : ℂ) : PowerSeries ℂ := logSingularityGF α * logGF

end AnalyticCombinatorics


