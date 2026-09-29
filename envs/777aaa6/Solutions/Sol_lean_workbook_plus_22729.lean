-- Prove2me | solution 1 for lean_workbook_plus_22729
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:34.125642+00:00
-- url     : https://prove2.me/submissions/6aa77323-8832-4377-9a8d-0b96181619cd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ f : ℝ → ℝ, (∀ x : ℝ, x ≠ 0 → f x / x ^ 2 = 0) → ∀ x : ℝ, x ≠ 0 → f x / x = 0 := by
  norm_num
