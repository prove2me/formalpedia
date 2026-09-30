-- Prove2me | solution 1 for lean_workbook_plus_70837
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:45.599259+00:00
-- url     : https://prove2.me/submissions/9b38e5bf-da51-48fe-bb8a-d7397c3e3acf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (h : a + b + c + d = 0) :
    (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ^ 2 =
      9 * (b * c - a * d) * (c * a - b * d) * (a * b - c * d) := by
  have hd : d = -(a + b + c) := by linarith
  rw [hd]
  ring

#print axioms solution
