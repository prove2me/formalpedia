-- Prove2me | solution 1 for lean_workbook_plus_50476
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:06.890604+00:00
-- url     : https://prove2.me/submissions/8c897c53-912e-4b70-a372-3315ed74e015

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x ≤ -1 then 2023 * x else -2022 * x ^ 2 -1) : ∃ x, ∃ y, x < y ∧ f x = f y := by
  refine ⟨-1, 1, by norm_num, ?_⟩
  subst hf
  norm_num
