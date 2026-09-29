-- Prove2me | solution 1 for lean_workbook_plus_33258
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:23.306555+00:00
-- url     : https://prove2.me/submissions/39c1540d-ee02-4157-8648-5ff471a1fe42

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 1/(x + 2) + 2/(y + 2) = 1/3) : x + 2*y ≥ 21 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
