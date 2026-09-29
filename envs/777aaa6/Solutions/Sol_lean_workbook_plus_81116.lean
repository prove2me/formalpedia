-- Prove2me | solution 1 for lean_workbook_plus_81116
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:42.735217+00:00
-- url     : https://prove2.me/submissions/309a6315-fdc9-436a-b824-f74e2b7922c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a = b) (h' : b = c) (h'' : c = a) : (a - b) / (1 - a * b) * a / (1 - a ^ 2) + (b - c) / (1 - b * c) * b / (1 - b ^ 2) + (c - a) / (1 - c * a) * c / (1 - c ^ 2) = 0 := by
  (intros; simp_all)
