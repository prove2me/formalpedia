-- Prove2me | solution 1 for lean_workbook_plus_58863
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:21.186304+00:00
-- url     : https://prove2.me/submissions/a669da24-d7e0-40c7-92c8-7100dab2aab6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + y + z = 1)
  (h₂ : x * y + x * z + y * z = 4 * x * y * z) :
  x + y + z ≥ 9 / 4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
