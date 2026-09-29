-- Prove2me | solution 1 for lean_workbook_plus_6331
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:31.886038+00:00
-- url     : https://prove2.me/submissions/156ad7b8-f487-4272-aaf8-31c5fdf01699

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) : s / 20 - s / 25 = s / 100 := by
  (intros; linarith)
