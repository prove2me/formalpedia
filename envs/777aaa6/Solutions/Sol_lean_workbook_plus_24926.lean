-- Prove2me | solution 1 for lean_workbook_plus_24926
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:32.54883+00:00
-- url     : https://prove2.me/submissions/18d9223c-0bde-4ea4-83c5-bb53f83f471f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) ≥ (a + 2 * b + c) / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
