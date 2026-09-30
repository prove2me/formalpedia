-- Prove2me | solution 1 for lean_workbook_plus_78123
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:54.482465+00:00
-- url     : https://prove2.me/submissions/e1af5dfa-903e-4dab-bc33-00a6548d48e7

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (x y : ℝ) :
  |x - f y| = |(x - f x) + (f x - f y)| ∧
  |x - f y| ≤ |x - f x| + |f x - f y| := by
  have e : x - f y = (x - f x) + (f x - f y) := by ring
  refine ⟨by rw [← e], ?_⟩
  rw [e]
  exact abs_add_le _ _
