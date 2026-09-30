-- Prove2me | solution 1 for lean_workbook_plus_58993
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:27.110179+00:00
-- url     : https://prove2.me/submissions/966d0b2f-cc6f-4a6d-919e-84a8861b846c

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x : ℝ, (x - 3) ^ 2 * (x + 6) ≥ 0) := by
  intro h
  have := h (-7)
  norm_num at this
