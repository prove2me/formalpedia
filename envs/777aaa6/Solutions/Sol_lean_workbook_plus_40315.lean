-- Prove2me | solution 1 for lean_workbook_plus_40315
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:53.501059+00:00
-- url     : https://prove2.me/submissions/cedb3f97-8472-4c11-93ec-c33d8665a540

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 3 / 8) (h₂ : b = 5 / 9) : a * b = 5 / 24 := by
  (intros; nlinarith)
