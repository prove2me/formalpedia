-- Prove2me | solution 1 for lean_workbook_plus_34396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:20.230633+00:00
-- url     : https://prove2.me/submissions/ac342d01-fb0e-4dbd-bd9d-2da22eb2aaf2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : (a^2 / (b-1) + b^2 / (a-1)) ≥ 8 := by
  have hx1 : 0 < a-1 := sub_pos.mpr ha
  have hy1 : 0 < b-1 := sub_pos.mpr hb
  have hs : 0 < a+b-2 := by linarith
  have h1 : a^2/(b-1)+b^2/(a-1)-(a+b)^2/(a+b-2) = (a*(a-1)-b*(b-1))^2/((a-1)*(b-1)*(a+b-2)) := by field_simp; ring
  have h2 : (a+b)^2/(a+b-2)-8 = (a+b-4)^2/(a+b-2) := by field_simp; ring
  have hp1 : 0 ≤ (a*(a-1)-b*(b-1))^2/((a-1)*(b-1)*(a+b-2)) := by positivity
  have hp2 : 0 ≤ (a+b-4)^2/(a+b-2) := by positivity
  linarith
