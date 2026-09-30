-- Prove2me | solution 1 for lean_workbook_plus_54450
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:38:21.481792+00:00
-- url     : https://prove2.me/submissions/66eb8ee9-4e0d-4b99-874d-3569a816ceb9

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 2 * (a * b^2 + b * c^2 + c * a^2 - a * b * c) * (a^2 * b + b^2 * c + c^2 * a - a * b * c)   := by
  have hsq := sq_nonneg ((a - b) * (b - c) * (c - a))
  have hgap : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) -
      2 * (a * b^2 + b * c^2 + c * a^2 - a * b * c) *
        (a^2 * b + b^2 * c + c^2 * a - a * b * c) =
      ((a - b) * (b - c) * (c - a))^2 := by ring
  linarith only [hsq, hgap]

#print axioms solution
