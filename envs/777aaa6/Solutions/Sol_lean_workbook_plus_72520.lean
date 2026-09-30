-- Prove2me | solution 1 for lean_workbook_plus_72520
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:10.157837+00:00
-- url     : https://prove2.me/submissions/3da4e524-1a1f-4c62-9399-6c4a6bbfb760

import Mathlib

set_option autoImplicit false

theorem solution (a b c : ℂ) (f : ℂ → ℂ)
    (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c) (h₁ : f 1 = 0) : c = -a - b := by
  have h := h₀ 1
  rw [h₁] at h
  norm_num at h
  linear_combination -h
