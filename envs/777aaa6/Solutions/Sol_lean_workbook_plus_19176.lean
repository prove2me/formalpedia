-- Prove2me | solution 1 for lean_workbook_plus_19176
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:06.807034+00:00
-- url     : https://prove2.me/submissions/b434eb95-7620-4bb0-9015-267d217e76d2

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y : ℝ, (x^3 / (x^2 + y^2) ≥ x - 1 / 2 * y)) := by
  intro h
  have := h 0 (-1)
  norm_num at this
