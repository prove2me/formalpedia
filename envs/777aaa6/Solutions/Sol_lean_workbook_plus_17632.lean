-- Prove2me | solution 1 for lean_workbook_plus_17632
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:19.747706+00:00
-- url     : https://prove2.me/submissions/ce0e2789-c7f6-4249-8004-34ed6b5d5a5f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : c ≠ 0) (h₂ : 3 * c = -2 * b - a) (h₃ : c = a - 2 * b) : c = -b := by
  (intros; linarith)
