-- Prove2me | solution 1 for lean_workbook_plus_13649
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:08.676942+00:00
-- url     : https://prove2.me/submissions/3876fbd5-dbb2-4fa4-9842-23095a56efff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x, f x = x): ∀ x, f x = x := by
  (intros; simp_all)
