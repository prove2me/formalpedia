-- Prove2me | solution 1 for WignerSemicircle.semicircleMoment_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:53:33.959814+00:00
-- url     : https://prove2.me/submissions/135a177a-c984-449d-8d7c-234e79960ca4

-- Sol generated from Probability/WignerSemicircleMoments.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
import Theorems.Thm_WignerSemicircle_semicircle_integral_eq
import Theorems.Thm_WignerSemicircle_sin_pow_mul_cos_sq_int
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


theorem sinPowInt_one : sinPowInt 1 = 0 := by
  simp [sinPowInt]

/-- The Wallis reduction formula on the symmetric interval: the boundary terms
vanish because `cos (±π/2) = 0`. -/
theorem sinPowInt_rec (m : ℕ) :
    sinPowInt (m + 2) = ((m : ℝ) + 1) / ((m : ℝ) + 2) * sinPowInt m := by
  have h := integral_sin_pow (a := -(π / 2)) (b := π / 2) m
  simp only [sinPowInt]
  rw [h]
  simp [Real.cos_pi_div_two]

theorem sinPowInt_odd (k : ℕ) : sinPowInt (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using sinPowInt_one
  | succ n ih =>
      have : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
      rw [this, sinPowInt_rec, ih, mul_zero]


/-! ### The trigonometric substitution -/



/-- Master formula for the semicircle moments in terms of Wallis integrals. -/
theorem semicircleMoment_eq (m : ℕ) :
    semicircleMoment m = 2 ^ (m + 2) / (2 * π) * (sinPowInt m - sinPowInt (m + 2)) := by
  rw [semicircleMoment, semicircle_integral_eq, sin_pow_mul_cos_sq_int]
  ring

/-! ### Odd moments vanish -/


/-! ### Even moments are Catalan numbers -/




/-! ### Small cases -/






open WignerSemicircle in
theorem solution(k : ℕ) : semicircleMoment (2 * k + 1) = 0 := by
  have h1 : sinPowInt (2 * k + 1) = 0 := sinPowInt_odd k
  have h2 : sinPowInt (2 * k + 1 + 2) = 0 := by
    have : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
    rw [this]; exact sinPowInt_odd (k + 1)
  rw [semicircleMoment_eq, h1, h2]
  ring
