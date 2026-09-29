-- Prove2me | solution 1 for lean_workbook_plus_26683
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:49.057203+00:00
-- url     : https://prove2.me/submissions/3c86bcb1-e9e9-465d-8af1-df0c449fd778

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : b ≠ 0)
  (h₁ : a ≠ 0) :
  (a / b + b / a)^2 - (a / b - b / a)^2 = 4 := by
  (intros; field_simp; ring)
