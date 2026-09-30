-- Prove2me | solution 1 for lean_workbook_plus_18565
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:51.513708+00:00
-- url     : https://prove2.me/submissions/e5a0b8ab-beda-49bb-ac47-7099f69ff51d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (z : ℂ) (h₀ : 5 * (z + 1 / z) = 26) :
    z = 1 / 5 ∨ z = 5 := by
  have hz : z ≠ 0 := by
    intro hz
    norm_num [hz] at h₀
  field_simp [hz] at h₀
  have hprod : (z - 5) * (5 * z - 1) = 0 := by linear_combination h₀
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inr (sub_eq_zero.mp h)
  · left
    linear_combination h / 5

#print axioms solution
