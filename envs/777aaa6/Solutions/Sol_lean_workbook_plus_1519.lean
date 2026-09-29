-- Prove2me | solution 1 for lean_workbook_plus_1519
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:05.795727+00:00
-- url     : https://prove2.me/submissions/0c0e6269-61de-469e-9556-d1de76a1f0a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (n : ℤ) : ⌊x + n⌋ = ⌊x⌋ + n := by
  norm_num
