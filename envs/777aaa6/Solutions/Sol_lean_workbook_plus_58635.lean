-- Prove2me | solution 1 for lean_workbook_plus_58635
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:47.094469+00:00
-- url     : https://prove2.me/submissions/7eb90253-58b8-45a0-8042-c00cafd67a8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (b - c) * (c - a) * (b - a) / (a + b) / (b + c) / (c + a) = (b - c) * (c - a) * (b - a) / (a + b) / (b + c) / (c + a) := by
  norm_num
