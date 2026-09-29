-- Prove2me | solution 1 for lean_workbook_plus_21178
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:20.772279+00:00
-- url     : https://prove2.me/submissions/d2448a16-2540-4274-99e7-1f89f39e31aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx: ∀ n, x n = n^(1/3)) : (x 2 - x 3) ^ 2 + (x 3 - x 4) ^ 2 + (x 4 - x 2) ^ 2 ≥ 0 := by
  (intros; simp_all)
