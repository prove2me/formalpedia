-- Prove2me | solution 1 for lean_workbook_plus_44417
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:57.654149+00:00
-- url     : https://prove2.me/submissions/459605b6-5395-468e-8de2-3b28081aa7fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
