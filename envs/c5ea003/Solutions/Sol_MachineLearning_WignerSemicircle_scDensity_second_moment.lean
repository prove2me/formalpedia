-- Prove2me | solution 1 for MachineLearning.WignerSemicircle.scDensity_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:18:30.868175+00:00
-- url     : https://prove2.me/submissions/6d52a4fe-5c46-4eb5-801e-0247af6c032c

-- Sol generated from MachineLearning/WignerSemicircle/Density.lean
import Mathlib
import Definitions.Def_MachineLearning_WignerSemicircle_Density
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Wigner Semicircle Density

This file develops the analytic side of the Wigner semicircle law: the density
of the (radius-1) semicircle distribution,

  f(x) = (2/π) · √(1 - x²),

supported on `[-1, 1]`.  This is the probability density towards which the
empirical spectral measures of normalized Wigner ensembles converge.  We prove it
is a genuine probability density (nonnegative, symmetric, integrates to `1`) and
compute its low-order moments (mean `0`, second moment `1/4`).

## Main results

- `scDensity_nonneg`        — the density is nonnegative.
- `scDensity_symm`          — the density is even (symmetry of the spectrum).
- `scDensity_eq_zero`       — the density vanishes outside `[-1, 1]` (compact support).
- `scDensity_normalization` — `∫_{-1}^{1} f = 1` (total probability mass).
- `scDensity_mean_zero`     — `∫_{-1}^{1} x · f(x) dx = 0` (mean of the law).
- `scDensity_second_moment` — `∫_{-1}^{1} x² · f(x) dx = 1/4` (variance of the law).
-/

open MachineLearning.WignerSemicircle

open scoped Real
open MeasureTheory intervalIntegral









open MachineLearning.WignerSemicircle in
theorem solution: ∫ x in (-1 : ℝ)..1, x ^ 2 * scDensity x = 1 / 4 := by
  have key : ∫ x in (-1 : ℝ)..1, x ^ 2 * Real.sqrt (1 - x ^ 2) = π / 8 := by
    calc ∫ x in (-1 : ℝ)..1, x ^ 2 * Real.sqrt (1 - x ^ 2)
        = ∫ x in Real.sin (-(π / 2))..Real.sin (π / 2), x ^ 2 * Real.sqrt (1 - x ^ 2) := by
            rw [Real.sin_neg, Real.sin_pi_div_two]
      _ = ∫ x in (-(π / 2))..(π / 2),
            (Real.sin x) ^ 2 * Real.sqrt (1 - (Real.sin x) ^ 2) * Real.cos x :=
            (integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_sin x)
              Real.continuousOn_cos (by fun_prop)).symm
      _ = ∫ x in (-(π / 2))..(π / 2), Real.sin x ^ 2 * Real.cos x ^ 2 := by
            refine integral_congr_ae (MeasureTheory.ae_of_all _ fun _ h => ?_)
            rw [Set.uIoc_of_le (neg_le_self (le_of_lt (half_pos Real.pi_pos))), Set.mem_Ioc] at h
            rw [← Real.cos_eq_sqrt_one_sub_sin_sq (le_of_lt h.1) h.2]; ring
      _ = π / 8 := by
            rw [integral_sin_sq_mul_cos_sq]
            have e1 : (4 : ℝ) * (π / 2) = 2 * π := by ring
            have e2 : (4 : ℝ) * (-(π / 2)) = -(2 * π) := by ring
            rw [e1, e2, Real.sin_neg, Real.sin_two_pi]
            ring
  have hpull : (∫ x in (-1 : ℝ)..1, x ^ 2 * scDensity x)
      = (2 / π) * ∫ x in (-1 : ℝ)..1, x ^ 2 * Real.sqrt (1 - x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x _
    unfold scDensity; ring
  rw [hpull, key]
  field_simp
  ring
