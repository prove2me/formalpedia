-- Prove2me | solution 2 for lean_workbook_plus_40882
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:41.211873+00:00
-- url     : https://prove2.me/submissions/bc781aa3-9a5b-4523-98be-63a12d36aceb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (2*x + y ≤ 10 ∧ 5*x + 2*y ≥ 20 ∧ -x + 2*y ≥ 0 ∧ x >= 0 ∧ y >= 0) → x + 3*y >= 7 := by
  (intros; linarith)
