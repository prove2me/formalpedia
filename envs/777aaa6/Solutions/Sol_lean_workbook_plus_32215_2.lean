-- Prove2me | solution 2 for lean_workbook_plus_32215
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:07.265083+00:00
-- url     : https://prove2.me/submissions/9f2a214d-ee2a-44c1-89e9-dd40b079152e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x^3 + 1 = 2 * x) :
  x^3 - 2 * x + 1 = 0 := by
  (intros; linarith)
