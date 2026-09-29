-- Prove2me | solution 1 for lean_workbook_plus_3919
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:29.720837+00:00
-- url     : https://prove2.me/submissions/d0ab5fa1-4c8d-40b7-a5e7-45a770ff2e3c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x ≤ 0 ∧ y ≤ 0 ∧ z ≤ 0 ∧ x * y * z = 1) :
  x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
