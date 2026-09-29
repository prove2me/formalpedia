-- Prove2me | solution 1 for lean_workbook_plus_23622
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:23.442782+00:00
-- url     : https://prove2.me/submissions/72365638-367e-4c59-b875-16d8a4ac3697

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a = 1) (h₂ : b = 0) : a^2 - 2 * b = 1 := by
  (intros; simp_all)
