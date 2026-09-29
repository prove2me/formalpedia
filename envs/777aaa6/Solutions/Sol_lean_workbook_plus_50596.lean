-- Prove2me | solution 1 for lean_workbook_plus_50596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:16.151708+00:00
-- url     : https://prove2.me/submissions/a593679f-8a1f-4da1-bbae-aab394b06656

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x^2*y - x*y^2 + y^2*z - y*z^2 + z^2*x - z*x^2)^2 ≥ 0 := by
  (intros; positivity)
