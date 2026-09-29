-- Prove2me | solution 1 for lean_workbook_plus_15980
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:39.315294+00:00
-- url     : https://prove2.me/submissions/2bd02f68-4cad-48c3-86b5-62715cfd4731

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 ≥ (a^3 + b^3 + c^3) / (a + b + c) + (2 / 3) * (a * b + b * c + c * a) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
