-- Prove2me | solution 1 for lean_workbook_plus_22281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:44.903227+00:00
-- url     : https://prove2.me/submissions/62e6a4d9-72b4-4c81-bf1e-52b3e64d5a75

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h1 : 3 < a) (h2 : 3 < b) (h3 : 3 < c) : a * b + b * c + c * a < a * b * c := by
  have ha : 0<a := by linarith
  have hb : 0<b := by linarith
  have hc : 0<c := by linarith
  have h1p := mul_pos (mul_pos ha hb) (sub_pos.mpr h3)
  have h2p := mul_pos (mul_pos hb hc) (sub_pos.mpr h1)
  have h3p := mul_pos (mul_pos hc ha) (sub_pos.mpr h2)
  nlinarith only [h1p,h2p,h3p]
