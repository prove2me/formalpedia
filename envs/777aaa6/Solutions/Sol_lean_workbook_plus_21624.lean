-- Prove2me | solution 1 for lean_workbook_plus_21624
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:43.821836+00:00
-- url     : https://prove2.me/submissions/2e958bf2-1557-4251-9702-367a983577c4

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (b * c) / (b ^ 5 + c ^ 5 + b * c) + (c * a) / (c ^ 5 + a ^ 5 + c * a) + (a * b) / (a ^ 5 + b ^ 5 + a * b) ≤ 1) := by
  intro h
  have := h (1/2) (1/2) (1/2)
  norm_num at this
