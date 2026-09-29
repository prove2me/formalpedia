-- Prove2me | solution 1 for lean_workbook_plus_55620
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:47.657335+00:00
-- url     : https://prove2.me/submissions/7075c3b8-c85b-448d-bdd5-529c6be468ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^2 + y^2 + z^2) ≥ 0 := by
  (intros; positivity)
