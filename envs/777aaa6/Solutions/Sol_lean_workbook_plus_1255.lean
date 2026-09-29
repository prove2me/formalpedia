-- Prove2me | solution 1 for lean_workbook_plus_1255
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:39.713688+00:00
-- url     : https://prove2.me/submissions/92332bf8-ae57-4e35-bf90-30554c2c948f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) ≥ (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
