-- Prove2me | solution 1 for lean_workbook_plus_79469
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:17.798646+00:00
-- url     : https://prove2.me/submissions/5a45a25d-8a6b-4aed-91d8-adf5e3d20bb3

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (hab : 1 < a ∧ 1 < b) : 2 * (a * b + 1) > (a + 1) * (b + 1) := by
  obtain ⟨ha, hb⟩ := hab
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]
