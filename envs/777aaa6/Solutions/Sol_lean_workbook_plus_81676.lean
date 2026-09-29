-- Prove2me | solution 1 for lean_workbook_plus_81676
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:42.59703+00:00
-- url     : https://prove2.me/submissions/0e84e8ec-83ac-4034-b38e-5e58efa43406

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + 1) / (b + 1) + (3 * a + b + 1) / (a + 3 * b + 1) + (6 * a + b + 1) / (a + 6 * b + 1) ≥ 1 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
