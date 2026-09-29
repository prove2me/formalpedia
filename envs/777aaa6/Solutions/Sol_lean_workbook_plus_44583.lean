-- Prove2me | solution 1 for lean_workbook_plus_44583
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:31.104458+00:00
-- url     : https://prove2.me/submissions/b586a095-4175-4339-ae21-ac42527b9d62

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : 2 < x ∧ x ≤ 3)
  (h₁ : y = x)
  (h₂ : z = x / (x - 2)) :
  (x - 2) * (x - 3)^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
