-- Prove2me | solution 1 for lean_workbook_plus_81851
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:48:07.351506+00:00
-- url     : https://prove2.me/submissions/0f331a9f-9553-4117-a93b-267f66742f0b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c)^2 / (a * b + b * c + c * a) ≥
      (a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) := by
  have hab := add_pos ha hb
  have hbc := add_pos hb hc
  have hca := add_pos hc ha
  have hq : 0 < a * b + b * c + c * a :=
    add_pos (add_pos (mul_pos ha hb) (mul_pos hb hc)) (mul_pos hc ha)
  have hid : (a + b + c)^2 / (a * b + b * c + c * a) -
      ((a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)) =
      (a * (a * b - b * c)^2 + b * (b * c - c * a)^2 + c * (c * a - a * b)^2) /
        ((a * b + b * c + c * a) * (a + b) * (b + c) * (c + a)) := by
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca, ne_of_gt hq,
      ne_of_gt (add_pos ha hc), ne_of_gt (add_pos hb ha), ne_of_gt (add_pos hc hb)]
    ring
  have hnum : 0 ≤ a * (a * b - b * c)^2 +
      b * (b * c - c * a)^2 + c * (c * a - a * b)^2 :=
    add_nonneg (add_nonneg (mul_nonneg ha.le (sq_nonneg _))
      (mul_nonneg hb.le (sq_nonneg _))) (mul_nonneg hc.le (sq_nonneg _))
  have hd := mul_pos (mul_pos (mul_pos hq hab) hbc) hca
  have hnonneg := div_nonneg hnum hd.le
  linarith
