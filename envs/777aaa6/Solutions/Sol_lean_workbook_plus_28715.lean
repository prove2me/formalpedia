-- Prove2me | solution 1 for lean_workbook_plus_28715
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:16.606586+00:00
-- url     : https://prove2.me/submissions/77ecf3c0-30d6-43de-b410-d07c6cfd8c0a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 1001 * c - 2002 * a = 4004)
  (h₁ : 1001 * b + 3003 * a = 5005) :
  (a + b + c) / 3 = 3 := by
  (intros; linarith)
