-- Prove2me | solution 1 for lean_workbook_plus_599
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:43.253083+00:00
-- url     : https://prove2.me/submissions/27ddbaed-93be-4137-8b89-5ed00374c02b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : |a - b|^2 = |(a - c) - (b - c)|^2 := by
  norm_num
