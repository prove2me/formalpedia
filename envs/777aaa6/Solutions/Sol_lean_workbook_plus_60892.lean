-- Prove2me | solution 1 for lean_workbook_plus_60892
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:32.053383+00:00
-- url     : https://prove2.me/submissions/451bba53-4daf-496f-be23-b498df8b9adb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : (x + y) ^ 2 + 1 - (x + y) + (3 * (x + y) - 2) * (x * y) + (x * y) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
