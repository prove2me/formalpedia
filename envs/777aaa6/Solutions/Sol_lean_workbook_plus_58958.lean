-- Prove2me | solution 1 for lean_workbook_plus_58958
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:05.820452+00:00
-- url     : https://prove2.me/submissions/f8b2862f-a263-45c6-9b22-71f7c86ea86a

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f 1 = 2 ∧ ∀ x y, f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y) : ∃ f : ℝ → ℝ, f 1 = 2 ∧ ∀ x y, f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y :=
  ⟨f, hf⟩
