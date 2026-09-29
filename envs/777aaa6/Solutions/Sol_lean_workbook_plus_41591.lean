-- Prove2me | solution 1 for lean_workbook_plus_41591
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:00.751974+00:00
-- url     : https://prove2.me/submissions/3b48f993-70d7-437b-a9a0-2e591f11fe07

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (t : ℝ)
  (h₀ : 0 < t) :
  Real.sqrt ((12 * t)^2 + (18 * t)^2) = 6 * Real.sqrt 13 * t := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 13)
  have hst := congrArg (fun s : ℝ => s*t^2) hs
  nlinarith
