-- Prove2me | solution 1 for lean_workbook_plus_67973
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:59.317418+00:00
-- url     : https://prove2.me/submissions/9fbc1f0b-a168-46cd-ad97-45d84b6c1819

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℝ) :
  (n^2 + 7) / (n^2 + 4) = 1 + 3 / (n^2 + 4) := by
  (intros; field_simp; ring)
