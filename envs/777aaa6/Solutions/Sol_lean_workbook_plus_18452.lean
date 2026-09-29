-- Prove2me | solution 1 for lean_workbook_plus_18452
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:37.770283+00:00
-- url     : https://prove2.me/submissions/d8b3ffed-c3e8-4242-add7-2aad7bc5ba63

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y) (h : 1 / (x * (x + 5 * y)) + 1 / (y * (y + 5 * x)) = 1) : x * y ≤ 1 / 3 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
