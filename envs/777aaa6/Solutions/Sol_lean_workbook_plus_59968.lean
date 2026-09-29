-- Prove2me | solution 1 for lean_workbook_plus_59968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:02.942781+00:00
-- url     : https://prove2.me/submissions/c6169b88-76fb-4b05-9d98-284d08b91034

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 1 < x) (hy : 1 < y) : x^2 / (y - 1) + y^2 / (x - 1) ≥ 8 := by
  have hx1 : 0 < x-1 := sub_pos.mpr hx
  have hy1 : 0 < y-1 := sub_pos.mpr hy
  have hs : 0 < x+y-2 := by linarith
  have h1 : x^2/(y-1)+y^2/(x-1)-(x+y)^2/(x+y-2) = (x*(x-1)-y*(y-1))^2/((x-1)*(y-1)*(x+y-2)) := by field_simp; ring
  have h2 : (x+y)^2/(x+y-2)-8 = (x+y-4)^2/(x+y-2) := by field_simp; ring
  have hp1 : 0 ≤ (x*(x-1)-y*(y-1))^2/((x-1)*(y-1)*(x+y-2)) := by positivity
  have hp2 : 0 ≤ (x+y-4)^2/(x+y-2) := by positivity
  linarith
