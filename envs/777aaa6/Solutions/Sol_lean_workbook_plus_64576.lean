-- Prove2me | solution 1 for lean_workbook_plus_64576
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:39.470791+00:00
-- url     : https://prove2.me/submissions/c989988d-fdc6-4587-93ea-aa19a543e4b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℚ) (h₁ : a = 5 / 2) (h₂ : b = 8 / 6) : a * b = 10 / 3 := by
  (intros; nlinarith)
