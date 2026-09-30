-- Prove2me | solution 1 for lean_workbook_plus_4777
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:48.93969+00:00
-- url     : https://prove2.me/submissions/cd56d47a-de69-4804-b364-3088577f4e1d

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, a^2 * b^2 * c^2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≤ (1 / (2^9)) * (a + b)^4 * (b + c)^4 * (c + a)^4) := by
  intro h
  have := h 1 (-1) 1
  ring_nf at this
  norm_num at this
