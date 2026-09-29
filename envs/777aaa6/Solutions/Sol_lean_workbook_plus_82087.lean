-- Prove2me | solution 1 for lean_workbook_plus_82087
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:56.921169+00:00
-- url     : https://prove2.me/submissions/10da1aca-52bd-4426-9827-d4c73e296673

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^4 + 4*y^4 = (x^2 + 2*x*y + 2*y^2) * (x^2 - 2*x*y + 2*y^2) := by
  (intros; linarith)
