-- Prove2me | solution 1 for lean_workbook_plus_27915
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:14.050079+00:00
-- url     : https://prove2.me/submissions/0cf2f558-c401-41c0-8b15-ea311ce041f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a * b = 0) : b * a = 0 := by
  (intros; linarith)
