-- Prove2me | solution 1 for lean_workbook_plus_76391
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:02.47879+00:00
-- url     : https://prove2.me/submissions/8b4834b8-3888-44da-abd2-c8a0e427aa5f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : a = 3 / x ∧ b = 3 / y ∧ c = 3 / z → a + b + c = 3 / x + 3 / y + 3 / z := by
  (intros; simp_all)
