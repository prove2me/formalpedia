-- Prove2me | solution 1 for lean_workbook_plus_47861
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:55.096879+00:00
-- url     : https://prove2.me/submissions/6654f4d5-c5aa-4a3b-90de-5fbc271cdc48

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (P : ℝ → ℝ) (h : P = λ x => 1007 * x ^ 2 - 2014 * x + 2014) : P 1 = 1007 := by
  (intros; simp_all)
