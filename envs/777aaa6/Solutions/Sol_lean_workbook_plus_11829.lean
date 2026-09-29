-- Prove2me | solution 1 for lean_workbook_plus_11829
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:46.032206+00:00
-- url     : https://prove2.me/submissions/eda73f60-7c98-4ab7-ba5f-c3d9ad019c5e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2007 * c / (2008 * a + 2009 * b) + 2008 * a / (2009 * b + 2007 * c) + 2009 * b / (2007 * c + 2008 * a)) ≥ 3 / 2 := by
  have nesbitt : ∀ x y z:ℝ, 0<x → 0<y → 0<z → 3/2 ≤ x/(y+z)+y/(z+x)+z/(x+y) := by
    intro x y z hx hy hz
    have hi : x/(y+z)+y/(z+x)+z/(x+y)-3/2 = ((x-y)^2*(x+y)+(y-z)^2*(y+z)+(z-x)^2*(z+x))/(2*(x+y)*(y+z)*(z+x)) := by field_simp; ring
    have hp : 0 ≤ ((x-y)^2*(x+y)+(y-z)^2*(y+z)+(z-x)^2*(z+x))/(2*(x+y)*(y+z)*(z+x)) := by positivity
    linarith
  simpa [add_comm,add_left_comm,add_assoc] using nesbitt (2007*c) (2008*a) (2009*b) (by positivity) (by positivity) (by positivity)
