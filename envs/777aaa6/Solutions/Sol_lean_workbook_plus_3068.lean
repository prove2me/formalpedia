-- Prove2me | solution 1 for lean_workbook_plus_3068
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:08.223743+00:00
-- url     : https://prove2.me/submissions/99075a72-02d6-4150-80c6-2049d3dc219a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) :
  (x - y)^2 ≥ 0 → x * y ≤ (x^2 + y^2) / 2 := by
  (intros; linarith)
