-- Prove2me | solution 1 for lean_workbook_plus_38913
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:10.177801+00:00
-- url     : https://prove2.me/submissions/2b57a548-e9e0-4258-974a-200c0549e060

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : a + c = b) (h₂ : a + d = c) (h₃ : b - d = 2) (h₄ : b + c - d = 3) : a + b + c + d = 4 := by
  (intros; linarith)
