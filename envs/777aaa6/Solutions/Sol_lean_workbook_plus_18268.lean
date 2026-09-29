-- Prove2me | solution 1 for lean_workbook_plus_18268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:26.13391+00:00
-- url     : https://prove2.me/submissions/2f6cca86-22bc-43cf-a3c5-0f57947c8834

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h s : ℝ)
  (h₀ : h - 1 / 5 * h = 12000)
  (h₁ : s + 1 / 5 * s = 12000) :
  h + s = 25000 := by
  (intros; linarith)
