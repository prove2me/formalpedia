-- Prove2me | solution 1 for lean_workbook_plus_77590
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:03:03.349361+00:00
-- url     : https://prove2.me/submissions/680aeeb1-1057-400b-a0a8-eada3a15339f

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ,
    2 * a * b + c ^ 2 ≥ 2 * a * b * c * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ↔
    a ^ 2 * (b + c) * (c - b) ^ 2 + b ^ 2 * (c + a) * (c - a) ^ 2 +
      (a + b) * (a * b - c ^ 2) ^ 2 ≥ 0) := by
  intro h
  have hh := h (-4) (-4) (-3)
  norm_num at hh
  change (32 : ℝ) + 9 < 276 / 7 at hh
  exact (by norm_num : ¬ ((32 : ℝ) + 9 < 276 / 7)) hh

#print axioms solution
