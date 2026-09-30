-- Prove2me | solution 1 for lean_workbook_plus_82179
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:07.327993+00:00
-- url     : https://prove2.me/submissions/2fd78ab9-6694-423d-90d3-200c92613c58

import Mathlib

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 →
    (a^2+b^2+c^2)^2 + (a*b+b*c+c*a)^2 ≥
      2 * (a^2+b^2+c^2) * (a*b+b*c+c*a) := by
  intro a b c _
  nlinarith only [sq_nonneg ((a^2+b^2+c^2) - (a*b+b*c+c*a))]
