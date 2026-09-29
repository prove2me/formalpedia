-- Prove2me | solution 1 for lean_workbook_plus_29381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:25.807269+00:00
-- url     : https://prove2.me/submissions/b73ef786-b811-43bc-ba38-895c76738847

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x^2 + y^2 + z^2 + 2 * x + 2 * y + 2 * z)^2 / (2 * (x^2 + y^2 + z^2) + 3) ≥ 0 := by
  (intros; positivity)
