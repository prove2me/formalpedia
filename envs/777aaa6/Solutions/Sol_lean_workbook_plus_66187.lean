-- Prove2me | solution 1 for lean_workbook_plus_66187
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:55.597807+00:00
-- url     : https://prove2.me/submissions/96b245f2-f005-4fc9-81b8-2bf735343632

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^3 + y^3 + z^3 + 2 * x * y * z)^2 ≥ 0 := by
  (intros; positivity)
