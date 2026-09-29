-- Prove2me | solution 1 for lean_workbook_plus_2797
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:06.504906+00:00
-- url     : https://prove2.me/submissions/cebda133-9d21-4c7f-afe4-06045d0af9e4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (5 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
