-- Prove2me | solution 1 for lean_workbook_plus_130
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:16.349372+00:00
-- url     : https://prove2.me/submissions/a7ede21c-41e3-4043-8cdb-e5f9a9494c04

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = if x ∈ Set.Icc 0 (1/3) then 0 else x - 1/3) : f x = if x ∈ Set.Icc 0 (1/3) then 0 else x - 1/3 := by
  (intros; simp_all)
