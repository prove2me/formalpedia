-- Prove2me | Definitions.Def_NumberTheory_ProfileFormPowerLaw
-- name    : NumberTheory_ProfileFormPowerLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:07.628894+00:00
-- url     : https://prove2.me/theorems/fa549c7b-6dbe-467c-8f2c-bf20bfec12d1
-- title:
--   Aether Catalog definitions — NumberTheory_ProfileFormPowerLaw
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ProfileFormPowerLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ProfileFormPowerLaw.lean by skeleton subtraction
import Mathlib

/-!
# Profile form: why the positional hit profile is a power law

Context (experiment 579, paper 229).  Re-analysis of `exp578_positions.npz`
(128 bit-length-96 semiprimes, 9594 recorded hits) fitted the small-`j` hit
profile `T` on the window `x ∈ [0, 2]` and found

* a **power law** `T(x) ≈ 0.0295 · (1 + x)^(-1.104)` with bootstrap CI
  `b ∈ [0.991, 1.218]` and Akaike weight `0.987`;
* the three rival one-dimensional families -- exponential (`ΔAICc +9.2`),
  logistic (`+11.5`, degenerate) and linear (`+16.9`) -- all lose.

This file isolates the *mathematics* behind that empirical verdict.  Nothing
here depends on the data: we prove that the power-law family is characterised
by an exact structural law, and that this structural law is incompatible with
each of the three rival families.

Main results.

* `powerProfile_scaleMul` — the power-law profile satisfies the *shift-scale
  multiplicativity* law
  `T 0 * T ((1+x)(1+y) - 1) = T x * T y`, i.e. it is multiplicative for the
  group law `x ⋆ y = (1+x)(1+y) - 1` on the shifted half-line.
* `powerProfile_of_scaleMultiplicative` — **rigidity**: *every* positive
  continuous profile obeying that law is a power law `A (1+x)^(-b)`.  This is
  the exact sense in which "the positional layer gets a law": the harmonic
  decline is forced, only the exponent is free.
* `powerProfile_exponent_unique` — the exponent is identifiable.
* `powerProfile_log_mid_strictConvex` — for `b > 0` the profile is *strictly*
  log-midpoint-convex: `T(t-h) · T(t+h) > T(t)^2`.
* `expProfile_log_mid_concave`, `logisticProfile_log_mid_concave`,
  `affineProfile_log_mid_concave` — each rival family satisfies the reverse
  inequality `f(t-h) · f(t+h) ≤ f(t)^2`.
* `powerProfile_ne_expProfile`, `powerProfile_ne_logisticProfile`,
  `powerProfile_ne_affineProfile` — hence a genuine power law (`b > 0`) is not
  a member of any of the three rival families: one single convexity invariant
  separates the winner from all three losers simultaneously.
* `declineFactor_bracket` — the window decline factor `T(0)/T(2) = 3^b` lies in
  `(2.8, 4.1)` for every `b` in the bootstrap interval `[0.991, 1.218]`,
  a bracket that contains the measured raw decline `3.25`.
-/

namespace ProfileForm

open Real

/-! ## The power-law profile and its structural law -/

/-- The fitted positional profile `T(x) = A · (1 + x)^(-b)`. -/
noncomputable def powerProfile (A b x : ℝ) : ℝ := A * (1 + x) ^ (-b)






/-! ## One convexity invariant separates the winner from all three losers

For a positive profile `f` put the *log-midpoint defect* at the three equally
spaced points `t - h < t < t + h`.  A power law with `b > 0` has
`f(t-h) f(t+h) > f(t)^2` (strict log-convexity), whereas exponential, logistic
and positive affine profiles all satisfy `f(t-h) f(t+h) ≤ f(t)^2`. -/

/-- Exponential rival family `C · exp (-k x)`. -/
noncomputable def expProfile (C k x : ℝ) : ℝ := C * Real.exp (-(k * x))

/-- Logistic rival family `C / (1 + exp (k (x - x₀)))`. -/
noncomputable def logisticProfile (C k x₀ x : ℝ) : ℝ :=
  C / (1 + Real.exp (k * (x - x₀)))

/-- Linear (affine) rival family `p + q x`. -/
def affineProfile (p q x : ℝ) : ℝ := p + q * x





/-! ### Separation corollaries -/




/-! ## The window decline factor

Over the measured window `x ∈ [0,2]` the power law declines by the factor
`T(0)/T(2) = 3^b`.  We bracket it over the bootstrap interval for `b`. -/

/-- The decline factor of the profile across the window `[0,2]`. -/
noncomputable def declineFactor (b : ℝ) : ℝ := (3:ℝ) ^ b







end ProfileForm


