-- Prove2me | solution 1 for lean_workbook_plus_76706
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:21.103599+00:00
-- url     : https://prove2.me/submissions/df87ca45-7219-4b5e-8537-8e43ac4784db

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 4 * x ^ 2 * y ^ 2 * z ^ 2 ≥ 0 := by
  (intros; positivity)
