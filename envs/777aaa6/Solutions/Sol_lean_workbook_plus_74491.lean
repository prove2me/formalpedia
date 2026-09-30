-- Prove2me | solution 1 for lean_workbook_plus_74491
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:35:58.47009+00:00
-- url     : https://prove2.me/submissions/53fd6f23-4b52-43b4-85a2-817a2d65d425

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ,
    (a * (a - b) * (a - c)) / (a ^ 2 + 2 * b * c) +
      (b * (b - a) * (b - c)) / (b ^ 2 + 2 * c * a) =
      (a - b) ^ 2 * (2 * a ^ 2 * c + 2 * b ^ 2 * c + a * b * c - a * c ^ 2 - b * c ^ 2) /
        ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a)) ∧
    (a - b) ^ 2 * (2 * a ^ 2 * c + 2 * b ^ 2 * c + a * b * c - a * c ^ 2 - b * c ^ 2) /
      ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a)) ≥ 0) := by
  intro h
  have bad := h 2 1 1
  norm_num at bad
