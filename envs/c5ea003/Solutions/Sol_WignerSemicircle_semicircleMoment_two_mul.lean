-- Prove2me | solution 1 for WignerSemicircle.semicircleMoment_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:26:31.716745+00:00
-- url     : https://prove2.me/submissions/8911c5a3-09c1-40a1-9fff-3b025bf1a802

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

theorem sinPowInt_zero : sinPowInt 0 = π := by
  simp [sinPowInt]


/-- The Wallis reduction formula on the symmetric interval: the boundary terms
vanish because `cos (±π/2) = 0`. -/
theorem sinPowInt_rec (m : ℕ) :
    sinPowInt (m + 2) = ((m : ℝ) + 1) / ((m : ℝ) + 2) * sinPowInt m := by
  have h := integral_sin_pow (a := -(π / 2)) (b := π / 2) m
  simp only [sinPowInt]
  rw [h]
  simp [Real.cos_pi_div_two]



/-! ### The trigonometric substitution -/



/-- Master formula for the semicircle moments in terms of Wallis integrals. -/
theorem semicircleMoment_eq (m : ℕ) :
    semicircleMoment m = 2 ^ (m + 2) / (2 * π) * (sinPowInt m - sinPowInt (m + 2)) := by
  rw [semicircleMoment, semicircle_integral_eq, sin_pow_mul_cos_sq_int]
  ring

/-! ### Odd moments vanish -/


/-! ### Even moments are Catalan numbers -/

/-- The Catalan recursion `(k+2) Cₖ₊₁ = 2(2k+1) Cₖ`. -/
theorem catalan_rec (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := Nat.succ_mul_centralBinom_succ k
  have h3 := succ_mul_catalan_eq_centralBinom k
  nlinarith [h1, h2, h3]

theorem semicircleMoment_two_mul_eq (k : ℕ) :
    semicircleMoment (2 * k) = 2 ^ (2 * k + 1) * sinPowInt (2 * k) / ((2 * (k : ℝ) + 2) * π) := by
  have hrec := sinPowInt_rec (2 * k)
  have hpi := Real.pi_ne_zero
  rw [semicircleMoment_eq, hrec]
  push_cast
  field_simp
  rw [show (2:ℝ) ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) by ring]
  ring


/-! ### Small cases -/






open WignerSemicircle in
theorem solution(k : ℕ) : semicircleMoment (2 * k) = catalan k := by
  induction k with
  | zero =>
      rw [semicircleMoment_two_mul_eq]
      simp [sinPowInt_zero, Real.pi_ne_zero]
  | succ n ih =>
      have hpi := Real.pi_ne_zero
      have hrec : sinPowInt (2 * (n + 1)) =
          ((2 * n : ℝ) + 1) / ((2 * n : ℝ) + 2) * sinPowInt (2 * n) := by
        have h : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [h, sinPowInt_rec]
        push_cast
        ring_nf
      have hcat : ((n : ℝ) + 2) * (catalan (n + 1) : ℝ) = 2 * (2 * n + 1) * (catalan n : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (catalan_rec n)
      rw [semicircleMoment_two_mul_eq, hrec]
      rw [semicircleMoment_two_mul_eq] at ih
      have hpow : (2 : ℝ) ^ (2 * (n + 1) + 1) = 4 * 2 ^ (2 * n + 1) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring]
        ring
      rw [hpow]
      push_cast
      push_cast at ih hcat
      field_simp at ih ⊢
      linear_combination (4 * (2 * (n : ℝ) + 1)) * ih - (4 * ((n : ℝ) + 1) * π) * hcat
