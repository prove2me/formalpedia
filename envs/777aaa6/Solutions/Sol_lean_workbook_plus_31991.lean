-- Prove2me | solution 1 for lean_workbook_plus_31991
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:45.642134+00:00
-- url     : https://prove2.me/submissions/fb1e8df3-3a36-44fc-8441-cd51d3c9a876

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (3*x - 2*y)^2 + (x - y + 2)^2 ≥ 0 := by
  (intros; positivity)
