-- Prove2me | solution 1 for WignerSemicircle.semicircle_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:20:21.608974+00:00
-- url     : https://prove2.me/submissions/5149314c-6f9a-43d5-9629-fd35ba3765ae

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
    (∫ x in (-2 : ℝ)..2, x ^ m * Real.sqrt (4 - x ^ 2)) =
      2 ^ (m + 2) * ∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m * Real.cos t ^ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (-(π / 2)) (π / 2),
      HasDerivAt (fun y => 2 * Real.sin y) (2 * Real.cos x) x :=
    fun x _ => (Real.hasDerivAt_sin x).const_mul 2
  have hcont : ContinuousOn (fun x : ℝ => 2 * Real.cos x) (Set.uIcc (-(π / 2)) (π / 2)) := by
    fun_prop
  have hg : Continuous (fun u : ℝ => u ^ m * Real.sqrt (4 - u ^ 2)) := by fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv hderiv hcont hg
  have he1 : 2 * Real.sin (-(π / 2)) = -2 := by simp
  have he2 : 2 * Real.sin (π / 2) = 2 := by simp
  rw [he1, he2] at h
  rw [← h]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  have hx' : x ∈ Set.Icc (-(π / 2)) (π / 2) := by
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
  have hcosnn : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc hx'
  have hsq : Real.sqrt (4 - (2 * Real.sin x) ^ 2) = 2 * Real.cos x := by
    have : 4 - (2 * Real.sin x) ^ 2 = (2 * Real.cos x) ^ 2 := by
      have := Real.sin_sq_add_cos_sq x
      nlinarith [this]
    rw [this, Real.sqrt_sq (by linarith)]
  simp only [Function.comp_apply]
  rw [hsq]
  rw [mul_pow]
  ring
