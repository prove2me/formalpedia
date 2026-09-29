-- Prove2me | solution 1 for lean_workbook_plus_81216
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:51.414645+00:00
-- url     : https://prove2.me/submissions/b11838a7-08b6-4154-a9e1-9339ac4437b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 1) : (x^2 - 2) / (x - 1)^3 = -1 / (x - 1)^3 + 2 / (x - 1)^2 + 1 / (x - 1) := by
  (intros; field_simp; ring)
