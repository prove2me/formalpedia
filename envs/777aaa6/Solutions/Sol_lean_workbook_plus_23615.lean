-- Prove2me | solution 1 for lean_workbook_plus_23615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:44.851682+00:00
-- url     : https://prove2.me/submissions/adf5d181-4d22-47af-97a9-6781aae77efd

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z t : ℝ) : x^4+y^4+z^4+t^4-4*x*y*z*t = (x-y)^2*(x+y)^2 + (z-t)^2*(z+t)^2 + 2*(x*y-z*t)^2 := by
  ring
