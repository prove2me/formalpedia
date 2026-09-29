-- Prove2me | solution 1 for lean_workbook_plus_53671
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:58.089336+00:00
-- url     : https://prove2.me/submissions/e882ad3c-86ae-4bb6-a210-4f369cdf77f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B : ℝ) (h : A ≥ B) : 2 * A ≥ A + B := by
  (intros; linarith)
