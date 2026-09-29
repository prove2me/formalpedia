-- Prove2me | solution 1 for lean_workbook_plus_43617
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:10.461595+00:00
-- url     : https://prove2.me/submissions/cc21dfa5-e490-4c5f-915b-ce48ee9907a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a > 0) (hb : b > 0) : (1 / (a + b)) ≤ (1 / (4 * a)) + (1 / (4 * b)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
