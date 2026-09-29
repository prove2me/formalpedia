-- Prove2me | solution 1 for lean_workbook_plus_51302
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:58.481163+00:00
-- url     : https://prove2.me/submissions/d54d17ed-e3a1-493e-a4f2-02fa075db4d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : -1 < x ∧ x < 8) : x ∈ Set.Ioo (-1) 8 := by
  (intros; simp_all)
