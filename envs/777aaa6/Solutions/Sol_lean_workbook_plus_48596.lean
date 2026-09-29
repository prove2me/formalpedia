-- Prove2me | solution 1 for lean_workbook_plus_48596
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:31.196791+00:00
-- url     : https://prove2.me/submissions/9acb4652-194a-4590-8e71-f4cd0e741ebb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h₁ : a > b) (h₂ : b > c) : 1 / (a - b) + 1 / (b - c) > 2 / (a - c) := by
  have hu : 0 < a-b := sub_pos.mpr h₁
  have hv : 0 < b-c := sub_pos.mpr h₂
  have hw : 0 < a-c := by linarith
  have hi : 1/(a-b)+1/(b-c)-2/(a-c) = ((a-b)^2+(b-c)^2)/((a-b)*(b-c)*(a-c)) := by field_simp; ring
  have hp : 0 < ((a-b)^2+(b-c)^2)/((a-b)*(b-c)*(a-c)) := by positivity
  linarith
