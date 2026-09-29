-- Prove2me | solution 1 for lean_workbook_plus_49903
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:13.112794+00:00
-- url     : https://prove2.me/submissions/8e513ebe-5453-4a03-9c31-20b34b6a112e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 10 / 8) (h₂ : b = 5 / 4) (h₃ : c = 2 / 2) : a = b * c := by
  (intros; nlinarith)
