-- Prove2me | solution 1 for lean_workbook_plus_63008
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:53.163674+00:00
-- url     : https://prove2.me/submissions/ec9b5d28-dbcd-4b33-878d-9f1a145b7b2a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) : (x - y) ^ 2 ≥ 0 := by
  (intros; positivity)
