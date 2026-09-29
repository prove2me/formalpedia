-- Prove2me | solution 1 for lean_workbook_plus_70810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:03.753814+00:00
-- url     : https://prove2.me/submissions/4ba7126a-b6dc-44ee-9b03-efc208aa1d02

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (F : ℝ → ℝ) (x : ℝ) (hf: F x = if x = 0 then 0 else 1) : F x = if x = 0 then 0 else 1 := by
  (intros; simp_all)
