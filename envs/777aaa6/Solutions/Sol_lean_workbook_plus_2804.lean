-- Prove2me | solution 1 for lean_workbook_plus_2804
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:13.281081+00:00
-- url     : https://prove2.me/submissions/fff46382-4a2f-4b35-9e89-139c41ccf5d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₀ : 2 ≤ x ∧ x ≤ 3) (h₁ : y = 4 - x) (h₂ : z = -1) : x^2 + y^2 + z^2 ≤ 11 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
