-- Prove2me | solution 1 for lean_workbook_plus_15093
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:12.745717+00:00
-- url     : https://prove2.me/submissions/d07d6c69-e979-4f26-be69-b1cb6863c79f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z ≥ 3) :
  (x + y + z - 3) * (2 * (x + y + z) - 3) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
