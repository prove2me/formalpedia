-- Prove2me | solution 1 for MachineLearning.WignerSemicircle.scDensity_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:01:49.718623+00:00
-- url     : https://prove2.me/submissions/e765ff07-06db-42a2-ae48-94130a12990d

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



/-- The semicircle density is even: `f(-x) = f(x)`. -/
theorem scDensity_symm (x : ℝ) : scDensity (-x) = scDensity x := by
  unfold scDensity; rw [show (1 : ℝ) - (-x) ^ 2 = 1 - x ^ 2 by ring]






open MachineLearning.WignerSemicircle in
theorem solution: ∫ x in (-1 : ℝ)..1, x * scDensity x = 0 := by
  have h1 : (∫ x in (-1 : ℝ)..1, (-x) * scDensity (-x)) = ∫ x in (-1 : ℝ)..1, x * scDensity x := by
    have h := integral_comp_neg (a := (-1 : ℝ)) (b := 1) (f := fun x => x * scDensity x)
    simpa using h
  have h2 : (∫ x in (-1 : ℝ)..1, (-x) * scDensity (-x)) = - ∫ x in (-1 : ℝ)..1, x * scDensity x := by
    rw [← intervalIntegral.integral_neg]
    apply integral_congr
    intro x _
    simp only
    rw [scDensity_symm]; ring
  rw [h2] at h1
  linarith
