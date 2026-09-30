-- Prove2me | solution 1 for lean_workbook_plus_66849
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:53:49.40513+00:00
-- url     : https://prove2.me/submissions/21d483d0-b7b9-4f9a-acf2-2e84ac92cc8d

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ,
    (Real.sqrt ((144 - x ^ 2) ^ 2) = 144 - x ^ 2) ↔ (0 ≤ 144 - x ^ 2) := by
  intro x
  rw [Real.sqrt_sq_eq_abs, abs_eq_self]

#print axioms solution
