-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
-- name    : AnalyticCombinatorics_Ch4_Analytic_LogSingularity
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:34.540031+00:00
-- url     : https://prove2.me/theorems/0a2bb87b-1418-4b15-8e16-3f83c5fd6bc6
-- title:
--   Algebraic and single-logarithmic coefficient models
-- statement:
--   Real and complex shifted harmonic sums are finite sums of totalized reciprocals of shifted parameters. The separately defined real and complex coefficient expressions multiply these sums by generalized binomial coefficients. The complex binomial series and the logarithmic series (zero constant coefficient and coefficient 1/n at positive n) define the single-log product formal series. These finite coefficient expressions are defined even at zero denominators; their equality to actual series coefficients requires the hypotheses of the separate identities.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/LogSingularity.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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
# Logarithmic singularity scale

This file adds the coefficient scale for the first logarithmic singular factor
over the standard function `(1 - z)^{-α}`.

For real `α > 1`, the exact `n`-th coefficient of
`(1 - z)^{-α} log (1 / (1 - z))` is

`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}`,

and it is asymptotic to `(n^(α - 1) / Γ α) * log n`.

The closed form is established directly from the exact parameter derivative of
the binomial coefficients (`logSingularityCoeff_isEquivalent`).  The final
section then proves the **genuine generating-function coefficient identity**
(`logSingularityCoeff_eq_coeff_logSingularityGF`): this closed form is exactly
the `n`-th coefficient of the Cauchy product of the honest power series for
`(1 - z)^{-α}` (Mathlib's `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`,
coefficients `Ring.choose (α + n - 1) n`) and for `log (1 / (1 - z))`
(coefficients `n⁻¹`), so the asymptotic is a genuine statement about the
log-singularity generating function rather than an asserted scale.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-- The shifted harmonic factor produced by differentiating the binomial scale in `α`. -/
def shiftedHarmonic (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (α + j)⁻¹

/--
Coefficient scale for `(1 - z)^{-α} log (1 / (1 - z))`.

The factor `shiftedHarmonic α n` is the logarithmic correction coming from
`∂_α Ring.choose (α + n - 1) n`.
-/
def logSingularityCoeff (α : ℝ) (n : ℕ) : ℝ :=
  Ring.choose (α + n - 1) n * shiftedHarmonic α n

/-!
## Genuine generating-function coefficient identity

The asymptotic above is stated for the *sequence*
`logSingularityCoeff α n = Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`.
The purpose of this section is to prove that this sequence is genuinely the
coefficient sequence of the log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))`, rather than merely an asserted scale.

We work over `ℂ`, where the two factor generating functions have honest
coefficient descriptions:

* `[zⁿ] (1 - z)^{-α} = Ring.choose (α + n - 1) n` — this is exactly the
  `n`-th coefficient of the analytic power series of `fun z ↦ 1 / (1 - z)^α`
  at `0`, banked in Mathlib as
  `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, whose formal
  multilinear series is `.ofScalars ℂ (fun n ↦ Ring.choose (α + n - 1) n)`.
* `[zⁿ] log (1 / (1 - z)) = [zⁿ] (-log (1 - z)) = n⁻¹` for `n ≥ 1` and `0`
  for `n = 0` — this is the standard logarithm expansion
  `∑ n, z^{n+1}/(n+1) = -log (1 - z)` (`Real`/`Complex.hasSum_pow_div_log…`).

We package these as formal power series and prove, by the Cauchy product
(`PowerSeries.coeff_mul`) together with a binomial/partial-fraction identity,
that the `n`-th coefficient of the product equals
`Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`, i.e. `logSingularityCoeff`.
-/

open scoped PowerSeries

/-- The genuine `n`-th coefficient of `(1 - z)^{-α}`. -/
def binCoeffℂ (α : ℂ) (n : ℕ) : ℂ := Ring.choose (α + n - 1) n

/-- The genuine `n`-th coefficient of `log (1 / (1 - z)) = -log (1 - z)`:
`0` at `n = 0` and `n⁻¹` for `n ≥ 1`. -/
def logCoeffℂ (n : ℕ) : ℂ := if n = 0 then 0 else (n : ℂ)⁻¹

/-- The generating function `(1 - z)^{-α}` as a formal power series, with the
genuine binomial coefficients. -/
noncomputable def oneSubCpowGF (α : ℂ) : ℂ⟦X⟧ := PowerSeries.mk (binCoeffℂ α)

/-- The generating function `log (1 / (1 - z))` as a formal power series, with
the genuine logarithmic coefficients. -/
noncomputable def logGF : ℂ⟦X⟧ := PowerSeries.mk logCoeffℂ

/-- The log-singularity generating function `(1 - z)^{-α} · log (1 / (1 - z))`
as a formal power series. -/
noncomputable def logSingularityGF (α : ℂ) : ℂ⟦X⟧ := oneSubCpowGF α * logGF

/-- The complex shifted-harmonic factor `∑_{j < n} (α + j)⁻¹`. -/
def shiftedHarmonicℂ (α : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, (α + j)⁻¹

/-- The complex log-singularity coefficient
`Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹`. -/
def logSingularityCoeffℂ (α : ℂ) (n : ℕ) : ℂ :=
  binCoeffℂ α n * shiftedHarmonicℂ α n


