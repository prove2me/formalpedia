-- Prove2me | solution 1 for lean_workbook_plus_56055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:21.879172+00:00
-- url     : https://prove2.me/submissions/40647a13-b2ae-488d-8376-1b3e07fbff0d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : y * (x - z) + (x - z) = -5 → (x - z) * (y + 1) = -5 := by
  (intros; linarith)
