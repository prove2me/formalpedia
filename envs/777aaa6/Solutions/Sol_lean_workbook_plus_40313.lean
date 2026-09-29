-- Prove2me | solution 1 for lean_workbook_plus_40313
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:32.665698+00:00
-- url     : https://prove2.me/submissions/8d423837-2511-43be-9bea-07508655acfe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  (intros; simp_all)
