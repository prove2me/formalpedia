-- Prove2me | solution 1 for lean_workbook_plus_22014
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:00.841655+00:00
-- url     : https://prove2.me/submissions/9d50697c-237c-43fe-ad7c-47909a8264a3

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 + (a - c) ^ 2 / (b ^ 2 + a * b + b * c + c * a) := by
  rw [ge_iff_le, ← sub_nonneg]
  have hD : 0 < b ^ 2 + a * b + b * c + c * a := by positivity
  have key : a / b + b / c + c / a - (3 + (a - c) ^ 2 / (b ^ 2 + a * b + b * c + c * a))
      = (a * (b ^ 2 - a * c) ^ 2 + b ^ 2 * (b + c) * (a - c) ^ 2)
        / (a * b * c * (b ^ 2 + a * b + b * c + c * a)) := by
    field_simp
    ring
  rw [key]
  positivity
