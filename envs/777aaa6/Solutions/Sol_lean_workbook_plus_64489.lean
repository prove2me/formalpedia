-- Prove2me | solution 1 for lean_workbook_plus_64489
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:43:38.665805+00:00
-- url     : https://prove2.me/submissions/6c33d25a-05a6-414b-9962-39fe69551b23

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ^ 2 + b ^ 2 ≥ c ^ 2 + d ^ 2) : b / (a + c) + a / (b + d) ≥ 1 := by
  have hac : 0 < a + c := by positivity
  have hbd : 0 < b + d := by positivity
  have hid : (b / (a + c) + a / (b + d) - 1) * (2 * (a + c) * (b + d)) =
      a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 + (a - b + c - d) ^ 2 := by
    field_simp [ne_of_gt hac, ne_of_gt hbd]
    <;> ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 2 * (a + c) * (b + d))
    (by rw [hid]; nlinarith [sq_nonneg (a - b + c - d)]) (by positivity)

#print axioms solution
