-- Prove2me | solution 1 for lean_workbook_plus_32397
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:01.945057+00:00
-- url     : https://prove2.me/submissions/88ff2c0c-7445-4fa2-a888-fa6c9a6a4b7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / (a + b + 1) < a / (a + 1) + b / (b + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
