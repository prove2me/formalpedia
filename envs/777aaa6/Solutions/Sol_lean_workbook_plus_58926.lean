-- Prove2me | solution 1 for lean_workbook_plus_58926
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:58.762025+00:00
-- url     : https://prove2.me/submissions/cf70ada9-1174-457c-9b68-9741d1ce28f9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem minimum_iff (a : ℝ) (ha : a < 2 ∧ 0 ≤ a) :
    a / (2 - a) + 2 / (a + 1) = 5 / 3 ↔ a = 1 / 2 := by
  have h1 : 0 < 2 - a := by linarith [ha.1]
  have h2 : 0 < a + 1 := by linarith [ha.2]
  have hd : 0 < 3 * (2 - a) * (a + 1) := mul_pos (mul_pos (by norm_num) h1) h2
  have hr : a / (2 - a) + 2 / (a + 1) - 5 / 3 =
      2 * (2 * a - 1) ^ 2 / (3 * (2 - a) * (a + 1)) := by
    field_simp
    ring
  constructor
  · intro h
    have hq : 2 * (2 * a - 1) ^ 2 / (3 * (2 - a) * (a + 1)) = 0 := by
      linarith
    have hz : (2 * a - 1) ^ 2 = 0 := by
      have := ((div_eq_zero_iff).mp hq).resolve_right hd.ne'
      nlinarith
    nlinarith
  · intro h
    subst a
    ring

theorem solution (a : ℝ) (ha : 2 > a ∧ a >= 0) :
    a / (2 - a) + 2 / (a + 1) ≥ 5 / 3 ∧
      (a = 1 / 2 → a / (2 - a) + 2 / (a + 1) = 5 / 3) := by
  have h1 : 0 < 2 - a := by linarith [ha.1]
  have h2 : 0 < a + 1 := by linarith [ha.2]
  have hr : a / (2 - a) + 2 / (a + 1) - 5 / 3 =
      2 * (2 * a - 1) ^ 2 / (3 * (2 - a) * (a + 1)) := by
    field_simp
    ring
  have hd : 0 < 3 * (2 - a) * (a + 1) := mul_pos (mul_pos (by norm_num) h1) h2
  constructor
  · have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg (2 * a - 1))) hd.le
    linarith
  · exact (minimum_iff a ha).mpr

#print axioms minimum_iff
#print axioms solution
