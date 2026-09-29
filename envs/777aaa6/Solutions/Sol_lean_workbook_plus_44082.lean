-- Prove2me | solution 1 for lean_workbook_plus_44082
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:46:59.3873+00:00
-- url     : https://prove2.me/submissions/9529e067-fe61-4ba5-959d-4358a039c4bf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (hx : x ≥ y) (hy : y ≥ z) (hz : z > 0) : x^2 * z + y^2 * z + z^2 * y + x * y * z > 0 := by
  have hy0 : 0 < y := lt_of_lt_of_le hz hy
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hx
  positivity
