-- Prove2me | solution 1 for lean_workbook_plus_32564
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:40.750043+00:00
-- url     : https://prove2.me/submissions/d2d96310-4a4b-4d15-9d34-f28c2d78ca51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ) :
  (2 * p^2 + p + 2)^2 - 5 * p^2 = 4 * (p^4 + p^3 + p^2 + p + 1) := by
  (intros; linarith)
