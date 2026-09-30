-- Prove2me | solution 1 for lean_workbook_plus_42969
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:37.358222+00:00
-- url     : https://prove2.me/submissions/6f50e720-ae69-4cd6-bde1-427362971403

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 2 * a^3 * b - 2 * b^3 * c - 2 * c^3 * a ≥ 0 := by
  have key : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 2 * a^3 * b - 2 * b^3 * c - 2 * c^3 * a
      = (a * (a - b))^2 + (b * (b - c))^2 + (c * (c - a))^2 := by ring
  rw [key]
  positivity
