-- Prove2me | solution 1 for lean_workbook_plus_40424
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:56.437713+00:00
-- url     : https://prove2.me/submissions/418afce0-e2fe-4bd6-ac44-96d657a0e24b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 / (a^2 + b * c) + b^2 / (b^2 + c * d) + c^2 / (c^2 + d * a) + d^2 / (d^2 + a * b) ≤ 3) := by
  have hi : 3-(a^2/(a^2+b*c)+b^2/(b^2+c*d)+c^2/(c^2+d*a)+d^2/(d^2+a*b))=(a^4*b^3*d+2*a^4*b*c*d^2+a^3*b*c^3*d+a^3*c*d^4+2*a^2*b^4*c*d+2*a^2*b^2*c^2*d^2+a*b^4*c^3+a*b^3*c*d^3+2*a*b^2*c^4*d+2*a*b*c^2*d^4+b*c^4*d^3)/((a^2+b*c)*(b^2+c*d)*(c^2+d*a)*(d^2+a*b)) := by field_simp; ring
  have hp : 0≤(a^4*b^3*d+2*a^4*b*c*d^2+a^3*b*c^3*d+a^3*c*d^4+2*a^2*b^4*c*d+2*a^2*b^2*c^2*d^2+a*b^4*c^3+a*b^3*c*d^3+2*a*b^2*c^4*d+2*a*b*c^2*d^4+b*c^4*d^3)/((a^2+b*c)*(b^2+c*d)*(c^2+d*a)*(d^2+a*b)) := by positivity
  linarith
