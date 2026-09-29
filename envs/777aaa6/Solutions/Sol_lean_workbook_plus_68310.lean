-- Prove2me | solution 1 for lean_workbook_plus_68310
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:44.403329+00:00
-- url     : https://prove2.me/submissions/826ca63c-266a-4f8c-acee-0ed596f5b246

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x_1 x_2 : ℝ) : (x_1 - x_2) ^ 2 ≥ 0 := by
  (intros; positivity)
