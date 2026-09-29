-- Prove2me | solution 1 for lean_workbook_plus_15108
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:10.058722+00:00
-- url     : https://prove2.me/submissions/5d29c1be-621e-40e7-923d-63bb3f8aa58a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c b : ℝ) : c^4 + b^4 ≥ c^3 * b + c * b^3 := by
  (intros; nlinarith [sq_nonneg (c), sq_nonneg (b), sq_nonneg (c - b), sq_nonneg (c + b)])
