-- Prove2me | solution 1 for lean_workbook_plus_63136
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:37:57.849181+00:00
-- url     : https://prove2.me/submissions/b659c65d-6014-4697-937c-18360230992a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (h1 : 2 * b ≥ a + c) (h2 : 2 * c ≥ b + d) (h3 : 2 * d ≥ c + a) (h4 : 2 * a ≥ d + b) : a + b + c + d ≤ 2 * (a + b) ∧ a + b + c + d ≤ 2 * (c + d) ∧ a + b + c + d ≤ 2 * (b + d) ∧ a + b + c + d ≤ 2 * (a + c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
