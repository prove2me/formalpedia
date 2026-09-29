-- Prove2me | solution 1 for lean_workbook_plus_36323
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:37.119029+00:00
-- url     : https://prove2.me/submissions/022b9cf9-dc2c-4aad-9f6d-6ae0af01c0ea

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : (a^4+b^4+c^4) ≥ max (a^3*b+b^3*c+c^3*a) (a*b^3+b*c^3+c*a^3) := by
  have one : ∀u v:ℝ,4*u^3*v≤3*u^4+v^4 := by
    intro u v
    have hp := mul_nonneg (sq_nonneg (u-v)) (show 0≤2*u^2+(u+v)^2 by positivity)
    nlinarith only [hp]
  apply max_le
  · nlinarith only [one a b,one b c,one c a]
  · nlinarith only [one b a,one c b,one a c]
