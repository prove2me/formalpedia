-- Prove2me | solution 1 for lean_workbook_plus_59417
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:23:25.911348+00:00
-- url     : https://prove2.me/submissions/cd862061-5d33-42dc-b23d-51302b639135

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

lemma root_determines_coefficients (r s : ℝ)
    (h : 2 * (3 + 2 * Complex.I) ^ 2 + r * (3 + 2 * Complex.I) + s = 0) :
    r = -12 ∧ s = 26 := by
  have hform : 2 * (3 + 2 * Complex.I) ^ 2 + r * (3 + 2 * Complex.I) + s =
      ((10 + 3 * r + s : ℝ) : ℂ) + ((24 + 2 * r : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination 8 * Complex.I_sq
  rw [hform] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Complex.mul_re, Complex.mul_im] at hr hi
  constructor
  · linear_combination (1 / 2 : ℝ) * hi
  · linear_combination hr - (3 / 2 : ℝ) * hi

theorem solution (r s : ℝ) (f : ℂ → ℂ)
    (h₀ : ∀ z, f z = 2 * z ^ 2 + r * z + s)
    (h₁ : f (3 + 2 * Complex.I) = 0) : s = 26 := by
  have h := h₀ (3 + 2 * Complex.I)
  rw [h₁] at h
  exact (root_determines_coefficients r s h.symm).2

#print axioms solution
