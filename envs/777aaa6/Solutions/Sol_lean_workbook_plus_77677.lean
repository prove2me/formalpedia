-- Prove2me | solution 1 for lean_workbook_plus_77677
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:54.677744+00:00
-- url     : https://prove2.me/submissions/36af8c55-2ffa-4d2f-9e98-9593316d3aea

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, (a ^ 2 * b * c ≠ 0 ∧ a * b * c ≠ 0) →
    b / c ^ 2 + c / a ^ 2 + a / b ^ 2 ≥ 1 / a + 1 / b + 1 / c) := by
  intro h
  have bad := h (-1) (-2) (-3) (by norm_num)
  norm_num at bad
