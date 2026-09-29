-- Prove2me | solution 1 for lean_workbook_plus_1881
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:17.809829+00:00
-- url     : https://prove2.me/submissions/bc5ec46b-9836-4821-b068-e026dcb08b0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : a + b = a^2 + b^2) : a + b ≤ a^2 + b^2 := by
  (intros; simp_all)
