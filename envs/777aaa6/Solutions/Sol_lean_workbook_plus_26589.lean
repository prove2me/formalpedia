-- Prove2me | solution 1 for lean_workbook_plus_26589
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:30.63049+00:00
-- url     : https://prove2.me/submissions/68fbf2c8-d079-4d58-a4ed-e2b502ed05ca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (C : ℝ) (h₁ : f = fun x => -x^4 / 2 - C * x + x / 2) : f = fun x => -x^4 / 2 - C * x + x / 2 := by
  (intros; simp_all)
