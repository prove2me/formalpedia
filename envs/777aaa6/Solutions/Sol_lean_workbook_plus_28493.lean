-- Prove2me | solution 1 for lean_workbook_plus_28493
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:31.25384+00:00
-- url     : https://prove2.me/submissions/8f9b4800-0e87-4ebf-b04d-26b5a8759dcf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ)
  (h₀ : 0 < k)
  (h₁ : 0 < 285 * Real.sqrt 3 / 8 * k^3)
  (h₂ : 0 < 147 * Real.sqrt 3 / 8 * k^3) :
  (147 * Real.sqrt 3 / 8 * k^3) / (285 * Real.sqrt 3 / 8 * k^3) = 49 / 95 := by
  (intros; field_simp; ring)
