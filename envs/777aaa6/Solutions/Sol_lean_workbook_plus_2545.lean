-- Prove2me | solution 1 for lean_workbook_plus_2545
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:51.644504+00:00
-- url     : https://prove2.me/submissions/44b5fb23-52e7-400e-94ff-080f5a3a3874

import Mathlib

theorem solution (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have hd : 0 < 2 * (a + b) * (b + c) * (c + a) := by positivity
  have hi :
      (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) *
        (2 * (a + b) * (b + c) * (c + a)) =
      (a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a) := by
    field_simp [ne_of_gt (add_pos hab hbc), ne_of_gt (add_pos hbc hca),
      ne_of_gt (add_pos hca hab)] <;> ring
  have hn : 0 ≤ (a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) +
      (c - a) ^ 2 * (c + a) := by positivity
  rw [← hi] at hn
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hd).mp hn)
