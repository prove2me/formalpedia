-- Prove2me | solution 1 for lean_workbook_plus_2657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:57.721462+00:00
-- url     : https://prove2.me/submissions/509bdbed-879b-436e-bfd0-401eb0fe2deb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : 2 * (x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2) = 2) : x = x ∧ y = y := by
  norm_num
