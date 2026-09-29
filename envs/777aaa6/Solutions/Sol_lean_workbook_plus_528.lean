-- Prove2me | solution 1 for lean_workbook_plus_528
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:40.960739+00:00
-- url     : https://prove2.me/submissions/9cfa37aa-ac65-4422-92f4-30ad00af5853

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (Int.fract x) = x - Int.floor x := by
  norm_num
