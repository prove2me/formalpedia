-- Prove2me | solution 1 for lean_workbook_plus_35489
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-04-09T20:46:14.46899+00:00
-- url     : https://prove2.me/submissions/be11f365-a24c-4355-b0fd-954cc4cdfeba

import Theorems.Thm_lean_workbook_plus_35489
import Mathlib.Tactic.Positivity

theorem solution (a : ℝ) : a ^ 2 ≥ 0 := by positivity
