-- Prove2me | solution 1 for lean_workbook_plus_57076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:41.290271+00:00
-- url     : https://prove2.me/submissions/9e5cb4bc-9b77-4fba-8db1-ca7637d24cbe

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a^2 * b + b^2 * c + c^2 * a)^2 ≥ 3 * (a^2 * c + a * b^2 + b * c^2) * a * b * c := by
  nlinarith [sq_nonneg (a^2*b - b^2*c), sq_nonneg (b^2*c - c^2*a), sq_nonneg (c^2*a - a^2*b)]
