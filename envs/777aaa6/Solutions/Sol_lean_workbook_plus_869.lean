-- Prove2me | solution 1 for lean_workbook_plus_869
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:44.511179+00:00
-- url     : https://prove2.me/submissions/ec79a804-0d64-4ea1-bede-810b6240fd73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / (a + 1) + b / (b + 1) ≥ (a + b) / (a + b + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
