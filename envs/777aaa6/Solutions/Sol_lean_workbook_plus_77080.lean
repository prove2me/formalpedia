-- Prove2me | solution 1 for lean_workbook_plus_77080
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:02.89405+00:00
-- url     : https://prove2.me/submissions/bf52b533-1c61-412c-a1c9-ebac70bd4559

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a * (1 - b) = 1 / 4) (hbc : b * (1 - c) = 1 / 4)
    (hca : c * (1 - a) = 1 / 4) : a = b ∧ b = c ∧ c = a := by
  have hfactor : 1 + a * b * c ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (mul_pos (mul_pos ha.1 ha.2.1) ha.2.2))
  have hcycle : (a - b) * (1 + a * b * c) = 0 := by
    linear_combination (1 + b) * hab + (a * b - 1) * hbc - (b + a * b) * hca
  have hab' : a = b := sub_eq_zero.mp ((mul_eq_zero.mp hcycle).resolve_right hfactor)
  have hbc' : b = c := by
    apply mul_left_cancel₀ (ne_of_gt ha.2.1)
    rw [hab'] at hab
    nlinarith [hab, hbc]
  exact ⟨hab', hbc', hbc'.symm.trans hab'.symm⟩

#print axioms solution
