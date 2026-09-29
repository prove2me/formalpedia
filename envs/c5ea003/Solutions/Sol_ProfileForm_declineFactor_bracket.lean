-- Prove2me | solution 1 for ProfileForm.declineFactor_bracket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:33.606889+00:00
-- url     : https://prove2.me/submissions/0a9c59fe-028c-4729-96c4-9c0335f8cc01

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




/-- Elementary upper bound `exp y ≤ (1 - y)⁻¹` for `y < 1`. -/
theorem exp_le_inv_one_sub {y : ℝ} (hy : y < 1) : Real.exp y ≤ (1 - y)⁻¹ := by
  have h1 : (0:ℝ) < 1 - y := by linarith
  have h2 : 1 - y ≤ Real.exp (-y) := by
    have := Real.add_one_le_exp (-y)
    linarith
  have h3 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [h3] at h2
  have hey : (0:ℝ) < Real.exp y := Real.exp_pos y
  exact (le_inv_comm₀ hey h1).mpr h2

theorem log_three_gt : (1.05 : ℝ) < Real.log 3 := by
  have hexp : Real.exp (1.05 : ℝ) < 3 := by
    have h1 : Real.exp (1.05 : ℝ) = Real.exp 1 * Real.exp 0.05 := by
      rw [← Real.exp_add]; norm_num
    have h2 : Real.exp (0.05 : ℝ) ≤ (1 - 0.05 : ℝ)⁻¹ := exp_le_inv_one_sub (by norm_num)
    have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h4 : (0:ℝ) < Real.exp 0.05 := Real.exp_pos _
    rw [h1]
    nlinarith
  have := Real.log_lt_log (Real.exp_pos _) hexp
  rwa [Real.log_exp] at this

theorem log_three_lt : Real.log 3 < (1.14 : ℝ) := by
  have hexp : (3:ℝ) < Real.exp (1.14 : ℝ) := by
    have h1 : Real.exp (1.14 : ℝ) = Real.exp 1 * Real.exp 0.14 := by
      rw [← Real.exp_add]; norm_num
    have h2 : (1.14 : ℝ) ≤ Real.exp 0.14 := by
      have := Real.add_one_le_exp (0.14 : ℝ); linarith
    have h3 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    rw [h1]
    nlinarith [Real.exp_pos (0.14 : ℝ)]
  have := Real.log_lt_log (by norm_num) hexp
  rwa [Real.log_exp] at this



open ProfileForm in
theorem solution{b : ℝ} (h1 : 0.991 ≤ b) (h2 : b ≤ 1.218) :
    2.8 < declineFactor b ∧ declineFactor b < 4.1 := by
  have hlog := log_three_gt
  have hlog' := log_three_lt
  constructor
  · have hexp : Real.exp (1.04 : ℝ) ≤ declineFactor b := by
      have : declineFactor b = Real.exp (b * Real.log 3) := by
        simp only [declineFactor]
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring_nf
      rw [this]
      apply Real.exp_le_exp.mpr
      calc (1.04:ℝ) ≤ 0.991 * 1.05 := by norm_num
        _ ≤ b * Real.log 3 :=
            mul_le_mul h1 hlog.le (by norm_num) (by linarith)
    have hlow : (2.8 : ℝ) < Real.exp (1.04 : ℝ) := by
      have h1' : Real.exp (1.04 : ℝ) = Real.exp 1 * Real.exp 0.04 := by
        rw [← Real.exp_add]; norm_num
      have h2' : (1.04 : ℝ) ≤ Real.exp 0.04 := by
        have := Real.add_one_le_exp (0.04 : ℝ); linarith
      have h3' : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      rw [h1']
      nlinarith [Real.exp_pos (0.04 : ℝ)]
    linarith
  · have hexp : declineFactor b ≤ Real.exp (1.3886 : ℝ) := by
      have : declineFactor b = Real.exp (b * Real.log 3) := by
        simp only [declineFactor]
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring_nf
      rw [this]
      apply Real.exp_le_exp.mpr
      calc b * Real.log 3 ≤ 1.218 * 1.14 :=
            mul_le_mul h2 hlog'.le (by linarith) (by norm_num)
        _ ≤ 1.3886 := by norm_num
    have hup : Real.exp (1.3886 : ℝ) < 4.1 := by
      have hstep : Real.exp (0.048575 : ℝ) ≤ (1 - 0.048575 : ℝ)⁻¹ :=
        exp_le_inv_one_sub (by norm_num)
      have hpow : Real.exp (0.3886 : ℝ) = (Real.exp (0.048575 : ℝ)) ^ (8:ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpow' : (Real.exp (0.048575:ℝ)) ^ (8:ℕ) ≤ ((1 - 0.048575 : ℝ)⁻¹) ^ (8:ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos _).le hstep 8
      have hb : Real.exp (0.3886:ℝ) ≤ ((1 - 0.048575 : ℝ)⁻¹) ^ (8:ℕ) := by
        rw [hpow]; exact hpow'
      have hnum : ((1 - 0.048575 : ℝ)⁻¹) ^ (8:ℕ) < 1.49 := by norm_num
      have h1' : Real.exp (1.3886 : ℝ) = Real.exp 1 * Real.exp 0.3886 := by
        rw [← Real.exp_add]; norm_num
      have h3' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      rw [h1']
      nlinarith [Real.exp_pos (0.3886:ℝ), Real.exp_pos (1:ℝ)]
    linarith
