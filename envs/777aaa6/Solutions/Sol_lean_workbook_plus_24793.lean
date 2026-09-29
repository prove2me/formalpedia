-- Prove2me | solution 1 for lean_workbook_plus_24793
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:47.685187+00:00
-- url     : https://prove2.me/submissions/e265fa68-e1b1-4b7b-9fd4-cb0161abd91d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r : ℝ) (h : 1 - 4 * (r - 1) ^ 2 ≥ 0) : 1 / 2 ≤ r ∧ r ≤ 3 / 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (r)])
