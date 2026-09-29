-- Prove2me | solution 1 for lean_workbook_plus_51034
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:32.480095+00:00
-- url     : https://prove2.me/submissions/f179e11d-b8c8-4723-adfd-fdf61e2cf99b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : y = x / Real.sqrt 3 ↔ y = x / Real.sqrt 3 := by
  norm_num
