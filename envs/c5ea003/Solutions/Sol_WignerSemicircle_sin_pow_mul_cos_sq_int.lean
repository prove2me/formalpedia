-- Prove2me | solution 1 for WignerSemicircle.sin_pow_mul_cos_sq_int
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:20:22.132848+00:00
-- url     : https://prove2.me/submissions/a2484bae-2144-45d3-9e51-deb5f94e8783

-- Sol generated from Probability/WignerSemicircleMoments.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Moments of the Wigner semicircle law are the Catalan numbers

This file establishes the analytic half of the moment method for the Wigner
semicircle law: the `m`-th moment of the standard semicircle distribution
(density `√(4 - x²)/(2π)` on `[-2, 2]`) vanishes for odd `m` and equals the
Catalan number `Cₖ` for `m = 2k`.

The proof runs through the trigonometric substitution `x = 2 sin t`, the
Mathlib reduction formula `integral_sin_pow`, and the Catalan recursion
`(k+2) Cₖ₊₁ = 2(2k+1) Cₖ` extracted from the central binomial coefficients.
-/

open Real intervalIntegral MeasureTheory
open scoped Nat

open WignerSemicircle

noncomputable section



/-! ### Wallis integrals on `[-π/2, π/2]` -/






/-! ### The trigonometric substitution -/




/-! ### Odd moments vanish -/


/-! ### Even moments are Catalan numbers -/




/-! ### Small cases -/






open WignerSemicircle in
theorem solution(m : ℕ) :
    (∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m * Real.cos t ^ 2) =
      sinPowInt m - sinPowInt (m + 2) := by
  have hcongr : (∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m * Real.cos t ^ 2) =
      ∫ t in (-(π / 2))..(π / 2), (Real.sin t ^ m - Real.sin t ^ (m + 2)) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    have := Real.sin_sq_add_cos_sq x
    simp only
    rw [pow_add]
    linear_combination (Real.sin x ^ m) * this
  rw [hcongr, sinPowInt, sinPowInt]
  refine intervalIntegral.integral_sub ?_ ?_ <;>
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
