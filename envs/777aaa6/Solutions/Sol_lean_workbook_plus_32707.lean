-- Prove2me | solution 1 for lean_workbook_plus_32707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:48.116991+00:00
-- url     : https://prove2.me/submissions/08e10c46-5b9c-45f3-9353-41b48ce741b0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≤ (a^3 + b^3 + c^3 + 6)^3 / 27 := by
  have one : ∀u v w:ℝ,0≤u → 0≤v → 0≤w → 27*u*v*w≤(u+v+w)^3 := by
    intro u v w hu hv hw
    have h1 := mul_nonneg (sq_nonneg (u+v-2*w)) (show 0≤u+v+w/4 by positivity)
    have h2 := mul_nonneg hw (sq_nonneg (u-v))
    nlinarith only [h1,h2]
  have hp := one (a^3+2) (b^3+2) (c^3+2) (by positivity) (by positivity) (by positivity)
  nlinarith only [hp]
