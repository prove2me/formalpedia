-- Prove2me | solution 1 for lean_workbook_plus_4593
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:16.079799+00:00
-- url     : https://prove2.me/submissions/aa891258-66ae-436d-88b2-7571afd5d7e7

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (2 / 3) * (a + b + c) ^ 2 ≥ a + b + c + a * b + b * c + c * a) := by
  intro h
  have := h (1/2) (1/2) (1/2)
  norm_num at this
