-- Prove2me | solution 1 for lean_workbook_plus_57986
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:34.295072+00:00
-- url     : https://prove2.me/submissions/25f80f58-5a48-475f-af1b-26cf8dcd3e85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : (3 / 2) * (1 / 4) = 3 / 8 := by
  norm_num
