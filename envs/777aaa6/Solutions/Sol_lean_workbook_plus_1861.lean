-- Prove2me | solution 1 for lean_workbook_plus_1861
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:33.096756+00:00
-- url     : https://prove2.me/submissions/448cbdc6-8fe1-4306-99c0-bc1953560064

import Mathlib

theorem solution : ¬ (∀ a b : ℝ, a * b ≥ 4 * a ^ 2 * b ^ 2 / (a + b) ^ 2) := by
  intro h
  have hc := h 1 (-2)
  norm_num at hc
