-- Prove2me | solution 1 for lean_workbook_plus_23063
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:31.36007+00:00
-- url     : https://prove2.me/submissions/2acb39fb-1e64-4ed2-8ba8-75f73761cc0a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : (1 + a ^ 2) ^ 4 ≥ (256 / 27) * a ^ 2 := by
  have hp := mul_nonneg (sq_nonneg (3*a^2-1)) (show 0≤3*a^4+14*a^2+27 by positivity)
  nlinarith only [hp]
