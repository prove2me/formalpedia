-- Prove2me | solution 1 for lean_workbook_plus_4901
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:40.974908+00:00
-- url     : https://prove2.me/submissions/6fd45f5d-34bc-40d1-b1df-86c4b350f51d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (m r s : ℂ) (f : ℂ → ℂ)
    (h₀ : ∀ x, f x = x^2 - (4 * m + 1) * x + 4 * m^2)
    (h₁ : f r = 0) (h₂ : f s = 0) (h₃ : r ≠ s) :
    r + s = 4 * m + 1 ∧ r * s = 4 * m^2 := by
  rw [h₀] at h₁ h₂
  have hprod : (r - s) * (r + s - (4 * m + 1)) = 0 := by
    linear_combination h₁ - h₂
  have hsum : r + s = 4 * m + 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h₃))
  refine ⟨hsum, ?_⟩
  linear_combination r * hsum - h₁

#print axioms solution
