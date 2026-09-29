-- Prove2me | solution 1 for lean_workbook_plus_61323
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:08.784166+00:00
-- url     : https://prove2.me/submissions/9633ed5d-ee6b-49e1-8b61-2c9b6265c92c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y z : ℝ} : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z) * (x^2 + y^2 + z^2 - x*y - x*z - y*z) := by
  (intros; linarith)
