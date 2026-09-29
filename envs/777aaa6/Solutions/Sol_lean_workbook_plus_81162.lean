-- Prove2me | solution 1 for lean_workbook_plus_81162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:14.596931+00:00
-- url     : https://prove2.me/submissions/eb5fdddf-3841-4227-ba17-02e666cbbcaf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (a ^ 2 + b ^ 2) + 2 / (a ^ 2 + 4 * b ^ 2)) ≤ (3 / (2 * a * b)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
