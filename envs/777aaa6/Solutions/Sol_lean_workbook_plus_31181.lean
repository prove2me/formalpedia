-- Prove2me | solution 1 for lean_workbook_plus_31181
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:29.240134+00:00
-- url     : https://prove2.me/submissions/feccfe62-abd2-4bb5-b1c4-2818ed2eb3d7

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ b c : ℝ, (b^2 + c^2)^2 - 5 * (b^2 - c^2)^2 ≥ 0) := by
  intro h
  have := h 1 0
  norm_num at this
