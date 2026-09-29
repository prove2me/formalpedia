-- Prove2me | solution 1 for lean_workbook_plus_67755
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:33.739292+00:00
-- url     : https://prove2.me/submissions/a0f504d5-e653-4a30-9be3-d1a9e2efef0f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x^2 - 14/15 * x - 4/5) : f = fun x => x^2 - 14/15 * x - 4/5 := by
  (intros; simp_all)
