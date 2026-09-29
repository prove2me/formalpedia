-- Prove2me | solution 1 for lean_workbook_plus_54983
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:13.226658+00:00
-- url     : https://prove2.me/submissions/4798cd92-e746-4700-926e-85af59b62f50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 3) : 4 * a + 4 * b + c = 3 * (a + b + 1) := by
  (intros; linarith)
