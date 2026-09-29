-- Prove2me | solution 1 for lean_workbook_plus_32074
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:26.508205+00:00
-- url     : https://prove2.me/submissions/d669c4c5-963f-4035-b81e-44eb3ab8a273

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (5 * a + b * (2 + b / a)) / (a + b) ≥ 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
