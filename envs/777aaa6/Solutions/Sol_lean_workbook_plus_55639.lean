-- Prove2me | solution 1 for lean_workbook_plus_55639
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:23.410418+00:00
-- url     : https://prove2.me/submissions/00dfd88c-9991-4177-817e-650f5448db91

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 20) (h₂ : b = 63 / 105) : a * b = 12 := by
  (intros; nlinarith)
