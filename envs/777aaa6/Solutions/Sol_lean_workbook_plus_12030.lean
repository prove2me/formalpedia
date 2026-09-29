-- Prove2me | solution 1 for lean_workbook_plus_12030
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:03.175381+00:00
-- url     : https://prove2.me/submissions/04abfe62-5517-4998-a1cf-666482919ab1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x = 1) : x - y^3 = 6 * (x - y^2) ↔ 1 - y^3 = 6 * (1 - y^2) := by
  (intros; simp_all)
