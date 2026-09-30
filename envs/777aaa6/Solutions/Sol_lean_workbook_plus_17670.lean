-- Prove2me | solution 1 for lean_workbook_plus_17670
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:12.509101+00:00
-- url     : https://prove2.me/submissions/31b01e90-8fcf-4a12-97e7-dabc55a57404

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x z : ℝ, 2 * x ^ 2 + 2 * z ^ 2 ≥ 4 * x * z := by
  intro x z
  nlinarith [sq_nonneg (x - z)]
