-- Prove2me | solution 1 for lean_workbook_plus_15043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:49.049383+00:00
-- url     : https://prove2.me/submissions/5841dd6d-93f2-4821-94a8-30427bcc89e9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (a^2 + 1) + 1 / (b^2 + 1) = 1 ↔ a * b = 1 := by
  have hda : 0 < a^2+1 := by positivity
  have hdb : 0 < b^2+1 := by positivity
  have hi : 1/(a^2+1)+1/(b^2+1)-1 = (1-(a*b)^2)/((a^2+1)*(b^2+1)) := by field_simp; ring
  constructor
  · intro h
    have hz : (1-(a*b)^2)/((a^2+1)*(b^2+1))=0 := by linarith
    have hn : 1-(a*b)^2=0 := (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt (mul_pos hda hdb))
    nlinarith [mul_pos ha hb]
  · intro h
    have hz : 1-(a*b)^2=0 := by rw [h]; norm_num
    rw [hz,zero_div] at hi
    linarith
