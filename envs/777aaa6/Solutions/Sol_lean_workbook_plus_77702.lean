-- Prove2me | solution 1 for lean_workbook_plus_77702
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:04.933104+00:00
-- url     : https://prove2.me/submissions/c76319b7-0f2c-412a-a5b8-f230ae34367c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ (x : ℝ), x ^ 2 - 7 = x - 1 →
    x = (1 + Real.sqrt 33) / 2 ∨ x = (1 - Real.sqrt 33) / 2) := by
  intro h
  have h3 : (3 : ℝ) ^ 2 - 7 = 3 - 1 := by ring
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 33)
  rcases h 3 h3 with hp | hm <;> nlinarith

#print axioms solution
