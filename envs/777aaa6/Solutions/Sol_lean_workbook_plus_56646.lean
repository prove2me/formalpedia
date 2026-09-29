-- Prove2me | solution 1 for lean_workbook_plus_56646
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:34.666033+00:00
-- url     : https://prove2.me/submissions/0504e34e-a2b0-4b84-94eb-2e1b01a3b13d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) * (1 / a + 1 / b) ≥ 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
