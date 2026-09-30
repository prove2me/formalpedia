-- Prove2me | solution 1 for lean_workbook_plus_60633
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:32.389756+00:00
-- url     : https://prove2.me/submissions/62be1f64-4c57-4d64-ba75-a1acb5a632b8

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ k : ℕ, ∀ z : Fin k → ℂ,
    ‖∑ i : Fin k, z i‖ ≤ ∑ i : Fin k, ‖z i‖ := by
  intro k z
  exact norm_sum_le _ _

#print axioms solution
