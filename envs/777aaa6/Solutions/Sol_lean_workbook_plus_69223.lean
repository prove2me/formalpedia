-- Prove2me | solution 1 for lean_workbook_plus_69223
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:47:53.67236+00:00
-- url     : https://prove2.me/submissions/9a590f8d-b8bd-4a19-9299-cf3c3095e317

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (M x y z v : ℝ) : M / (7 * y * z^2) = 1 / 7 * (M / (y * z^2)) := by
  (intros; ring)
