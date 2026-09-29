-- Prove2me | solution 1 for lean_workbook_plus_46596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:46.27498+00:00
-- url     : https://prove2.me/submissions/218f3aad-0c5d-412e-af10-695c3f69717d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (b - c) ^ 2 * (b + c - 2 * a) ^ 2 + (c - a) ^ 2 * (c + a - 2 * b) ^ 2 + (a - b) ^ 2 * (a + b - 2 * c) ^ 2 = 1 / 2 * ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) ^ 2 := by
  (intros; linarith)
