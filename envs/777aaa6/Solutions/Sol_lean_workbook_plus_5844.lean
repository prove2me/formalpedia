-- Prove2me | solution 1 for lean_workbook_plus_5844
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:55.500133+00:00
-- url     : https://prove2.me/submissions/6e01cf4b-2ea9-4610-96c1-5308e77ec733

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (b - a) / a * 100 = (100 * (b - a)) / a := by
  (intros; ring)
