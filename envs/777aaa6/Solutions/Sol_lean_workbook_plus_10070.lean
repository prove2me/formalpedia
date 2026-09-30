-- Prove2me | solution 1 for lean_workbook_plus_10070
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:09.243294+00:00
-- url     : https://prove2.me/submissions/f89b0b0c-3916-4b05-9212-797cc9de7c06

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a:ℝ, (1 - a) ^ 2 * (10 - a) ≥ 0) := by
  intro h
  have := h 11
  norm_num at this
