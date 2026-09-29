-- Prove2me | solution 1 for lean_workbook_plus_4358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:58:29.423511+00:00
-- url     : https://prove2.me/submissions/40c30204-a47f-4e1f-b754-ba5662d1290c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) : (a + 1) / (b + 2) + (b + 1) / (a + 2) ≤ 3 / 2 := by
  have hda : 0 < a+2 := by linarith [ha.1]
  have hdb : 0 < b+2 := by linarith [hb.1]
  have hp := mul_nonneg (show 0 ≤ a-1 by linarith [ha.1]) (show 0 ≤ 2-a by linarith [ha.2])
  have hq := mul_nonneg (show 0 ≤ b-1 by linarith [hb.1]) (show 0 ≤ 2-b by linarith [hb.2])
  have hr := mul_nonneg (show 0 ≤ 2-a by linarith [ha.2]) (show 0 ≤ 2-b by linarith [hb.2])
  have hn : 0 ≤ 3*a*b-2*a^2-2*b^2+4 := by nlinarith
  have he : 3/2-((a+1)/(b+2)+(b+1)/(a+2)) = (3*a*b-2*a^2-2*b^2+4)/(2*(a+2)*(b+2)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb]
    <;> ring
  have hpos : 0 ≤ (3*a*b-2*a^2-2*b^2+4)/(2*(a+2)*(b+2)) := div_nonneg hn (by positivity)
  linarith
