-- Prove2me | solution 1 for lean_workbook_plus_50819
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:59.423613+00:00
-- url     : https://prove2.me/submissions/65d97e45-2f63-424e-9991-ef2206f3cba6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 4/7) (h₂ : b = 5/11) : a * b = 20/77 := by
  (intros; nlinarith)
