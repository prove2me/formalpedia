-- Prove2me | solution 1 for lean_workbook_plus_35625
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:49.284157+00:00
-- url     : https://prove2.me/submissions/52e420ea-27d7-48d0-80b9-1def86bbfddb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (2 * (a + b)) + 1 / (3 * (b + c)) + 1 / (6 * (c + a)) ≥ 6 / (4 * a + 5 * b + 3 * c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
