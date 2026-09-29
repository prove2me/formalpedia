-- Prove2me | solution 1 for lean_workbook_plus_66226
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:58.064425+00:00
-- url     : https://prove2.me/submissions/fd29a9b5-8cf7-40ca-b40e-8d01b45e5145

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℂ) (x : ℝ) : (1 + x) + x * Complex.I = (1 + x) + (0 + x) * Complex.I := by
  norm_num
