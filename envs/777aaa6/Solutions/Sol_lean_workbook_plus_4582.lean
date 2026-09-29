-- Prove2me | solution 1 for lean_workbook_plus_4582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:24.058356+00:00
-- url     : https://prove2.me/submissions/e744cb34-f74c-49d7-86f9-1d82ce769d14

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : a ≥ 2) (hb : b ≥ 2) (hc : c ≥ 2) (hd : d ≥ 2) (habc : (a - 1) * (b - 1) * (c - 1) * (d - 1) = 1) : 1 / a + 1 / b + 1 / c + 1 / d ≥ 2 := by
  have bound (u v w t : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (ht : 1 ≤ t) : u ≤ u*v*w*t := by
    calc
      u = u*1*1*1 := by ring
      _ ≤ u*v*w*t := by gcongr <;> linarith
  have ha1 : 1 ≤ a-1 := by linarith
  have hb1 : 1 ≤ b-1 := by linarith
  have hc1 : 1 ≤ c-1 := by linarith
  have hd1 : 1 ≤ d-1 := by linarith
  have ha2 : a=2 := by nlinarith [bound (a-1) (b-1) (c-1) (d-1) ha1 hb1 hc1 hd1]
  have hb2 : b=2 := by nlinarith [bound (b-1) (c-1) (d-1) (a-1) hb1 hc1 hd1 ha1]
  have hc2 : c=2 := by nlinarith [bound (c-1) (d-1) (a-1) (b-1) hc1 hd1 ha1 hb1]
  have hd2 : d=2 := by nlinarith [bound (d-1) (a-1) (b-1) (c-1) hd1 ha1 hb1 hc1]
  rw [ha2,hb2,hc2,hd2]
  norm_num
