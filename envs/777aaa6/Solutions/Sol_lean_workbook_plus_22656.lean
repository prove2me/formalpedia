-- Prove2me | solution 1 for lean_workbook_plus_22656
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:05.516571+00:00
-- url     : https://prove2.me/submissions/c440e4e8-ff16-4290-ab90-731a80a7a9e4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h1 : a > b) (h2 : b > 0) (h3 : a^5 + b^5 = a - b) : a^4 + b^4 < 1 := by
  have ha : 0<a := lt_trans h2 h1
  have hd : 0<a-b := sub_pos.mpr h1
  have hp : 0<b*a*(a-b)*(a^2+a*b+b^2)+2*b^5 := by positivity
  have hi : (a-b)*(a^4+b^4)<a-b := by nlinarith only [hp,h3]
  by_contra hn
  have he := mul_le_mul_of_nonneg_left (show 1≤a^4+b^4 by linarith) hd.le
  nlinarith only [he,hi]
