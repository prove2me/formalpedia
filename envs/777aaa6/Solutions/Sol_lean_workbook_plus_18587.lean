-- Prove2me | solution 1 for lean_workbook_plus_18587
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:42.897966+00:00
-- url     : https://prove2.me/submissions/325d0efc-ac22-45b0-a9ce-dc673b04d6d4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) : x * y + y * z + z * x ≤ 2 * x * y * z + 1 := by
  have hx1 : 0 < x-1 := sub_pos.mpr hx
  have hy1 : 0 < y-1 := sub_pos.mpr hy
  have hz1 : 0 < z-1 := sub_pos.mpr hz
  have h1 : 0 ≤ (x-1)*(y-1) := by positivity
  have h2 : 0 ≤ (y-1)*(z-1) := by positivity
  have h3 : 0 ≤ (z-1)*(x-1) := by positivity
  have h4 : 0 ≤ (x-1)*(y-1)*(z-1) := by positivity
  nlinarith only [h1,h2,h3,h4]
