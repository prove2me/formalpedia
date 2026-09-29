-- Prove2me | solution 1 for lean_workbook_plus_23615
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:21.002652+00:00
-- url     : https://prove2.me/submissions/1be82d71-e821-4db0-8860-e80b0568571e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) : x^4+y^4+z^4+t^4-4*x*y*z*t = (x-y)^2*(x+y)^2 + (z-t)^2*(z+t)^2 + 2*(x*y-z*t)^2 := by
  (intros; linarith)
