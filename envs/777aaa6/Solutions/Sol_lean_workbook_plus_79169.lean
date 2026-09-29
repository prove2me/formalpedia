-- Prove2me | solution 1 for lean_workbook_plus_79169
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:55.586398+00:00
-- url     : https://prove2.me/submissions/a4cddcad-6605-48e9-a244-9886b1b052a3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x ≠ 0 → 1/x * (x^2 / 2 - 1 / (2 * x)) + (1 / (2 * x^2) + x / 2) = x := by
  (intros; field_simp; ring)
