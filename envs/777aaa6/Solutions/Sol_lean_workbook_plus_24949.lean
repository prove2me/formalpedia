-- Prove2me | solution 1 for lean_workbook_plus_24949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:58.424698+00:00
-- url     : https://prove2.me/submissions/f660bef2-900a-43f0-af34-63abbb1f6ebb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z r : ℝ) (u v w : ℝ) (h1 : u^2 + v^2 + w^2 = 1) (h2 : x = r * u) (h3 : y = r * v) (h4 : z = r * w) : x^2 + y^2 + z^2 = r^2 := by
  rw [h2, h3, h4]
  nlinarith [congrArg (fun t : ℝ => r^2*t) h1]
