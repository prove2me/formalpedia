-- Prove2me | solution 1 for lean_workbook_plus_78080
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:59.942759+00:00
-- url     : https://prove2.me/submissions/5a75e164-ab00-499c-8836-35e2166c47ef

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ,
    a ^ 3 * (b ^ 2 - c ^ 2) ^ 2 + b ^ 3 * (c ^ 2 - a ^ 2) ^ 2 +
      c ^ 3 * (a ^ 2 - b ^ 2) ^ 2 ≥ 0) := by
  intro h
  have bad := h (-1) (-2) (-3)
  norm_num at bad
