-- Prove2me | solution 1 for lean_workbook_plus_35918
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:07.712886+00:00
-- url     : https://prove2.me/submissions/8970ffb3-29fe-400e-a1ae-2541170e4fe3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x > 0) (h₂ : y - x > 1) : y > x + 1 := by
  (intros; linarith)
