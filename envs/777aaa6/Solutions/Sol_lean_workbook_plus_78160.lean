-- Prove2me | solution 1 for lean_workbook_plus_78160
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:12:03.662644+00:00
-- url     : https://prove2.me/submissions/803772bf-c2a6-4d13-bc11-8cfa60af0903

import Mathlib
set_option autoImplicit false
theorem solution (x : ℝ) (f : ℝ → ℝ) (h₁ : ∀ x, f (-x) = f x) (h₂ : ∀ x, f (2 * x) = 3 * f x + x) : f 0 + 2 * f (2 * x) = 3 * f x + x := by
  have h0 := h₂ 1
  have hneg := h₂ (-1)
  have he1 := h₁ 1
  have he2 := h₁ 2
  norm_num at h0 hneg he1 he2
  linarith
