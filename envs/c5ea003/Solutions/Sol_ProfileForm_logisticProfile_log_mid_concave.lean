-- Prove2me | solution 1 for ProfileForm.logisticProfile_log_mid_concave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:31:56.567752+00:00
-- url     : https://prove2.me/submissions/a093dcbf-338a-4836-aefd-3e60afa68596

-- Sol generated from NumberTheory/ProfileFormPowerLaw.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

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

open ProfileForm

open Real

/-! ## The power-law profile and its structural law -/







/-! ## One convexity invariant separates the winner from all three losers

For a positive profile `f` put the *log-midpoint defect* at the three equally
spaced points `t - h < t < t + h`.  A power law with `b > 0` has
`f(t-h) f(t+h) > f(t)^2` (strict log-convexity), whereas exponential, logistic
and positive affine profiles all satisfy `f(t-h) f(t+h) ≤ f(t)^2`. -/








/-! ### Separation corollaries -/




/-! ## The window decline factor

Over the measured window `x ∈ [0,2]` the power law declines by the factor
`T(0)/T(2) = 3^b`.  We bracket it over the bootstrap interval for `b`. -/









open ProfileForm in
theorem solution{C k t h x₀ : ℝ} (hC : 0 < C) :
    logisticProfile C k x₀ (t - h) * logisticProfile C k x₀ (t + h)
      ≤ logisticProfile C k x₀ t ^ 2 := by
  set u : ℝ := k * (t - x₀) with hu
  have e1 : k * (t - h - x₀) = u - k * h := by rw [hu]; ring
  have e2 : k * (t + h - x₀) = u + k * h := by rw [hu]; ring
  simp only [logisticProfile, e1, e2, ← hu]
  have hpu : (0:ℝ) < Real.exp u := Real.exp_pos u
  have hp1 : (0:ℝ) < 1 + Real.exp (u - k * h) := by positivity
  have hp2 : (0:ℝ) < 1 + Real.exp (u + k * h) := by positivity
  have hp3 : (0:ℝ) < 1 + Real.exp u := by positivity
  have hsplit : Real.exp (u - k * h) * Real.exp (u + k * h) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hsum : 2 * Real.exp u ≤ Real.exp (u - k * h) + Real.exp (u + k * h) := by
    have h2 : Real.exp (u - k * h) + Real.exp (u + k * h)
        = Real.exp u * (Real.exp (-(k * h)) + Real.exp (k * h)) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_neg]; field_simp
    have hcosh : 2 ≤ Real.exp (-(k * h)) + Real.exp (k * h) := by
      have hE : (0:ℝ) < Real.exp (k * h) := Real.exp_pos _
      have hinv : Real.exp (-(k * h)) = (Real.exp (k * h))⁻¹ := Real.exp_neg _
      have hipos : (0:ℝ) < (Real.exp (k * h))⁻¹ := inv_pos.mpr hE
      have hmul : (Real.exp (k * h))⁻¹ * Real.exp (k * h) = 1 :=
        inv_mul_cancel₀ (ne_of_gt hE)
      rw [hinv]
      nlinarith [mul_nonneg hipos.le (sq_nonneg (Real.exp (k * h) - 1)), hmul, hE, hipos]
    rw [h2]
    nlinarith [hpu]
  have hkey : (1 + Real.exp u) ^ 2
      ≤ (1 + Real.exp (u - k * h)) * (1 + Real.exp (u + k * h)) := by
    nlinarith [hsplit, hsum, hpu]
  have hrewrite : C / (1 + Real.exp (u - k * h)) * (C / (1 + Real.exp (u + k * h)))
      = C ^ 2 / ((1 + Real.exp (u - k * h)) * (1 + Real.exp (u + k * h))) := by
    field_simp
  rw [hrewrite, div_pow]
  gcongr
