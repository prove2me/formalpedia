-- Prove2me | solution 1 for lean_workbook_plus_81074
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:58:22.183283+00:00
-- url     : https://prove2.me/submissions/b67721c3-23dd-4be6-a144-2098d7898685

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x ≠ 0) :
    (1 / (x + 1 / (1 + 1 / 2)) =
      1 / (2 + 1 / (1 - 1 / (2 + 1 / 2)))) ↔ x = 3 := by
  constructor
  · intro h
    have hi := congrArg (fun t : ℝ => t⁻¹) h
    norm_num at hi
    linarith
  · rintro rfl
    norm_num
