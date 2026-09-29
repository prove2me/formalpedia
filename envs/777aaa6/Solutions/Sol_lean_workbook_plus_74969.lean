-- Prove2me | solution 1 for lean_workbook_plus_74969
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:39.555344+00:00
-- url     : https://prove2.me/submissions/d565472a-7889-417b-a1d3-53581510ede7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 3 / 8) (h₂ : b = 5 / 7) : a * b = 15 / 56 := by
  (intros; nlinarith)
