-- Prove2me | solution 1 for lean_workbook_plus_81836
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:55.259191+00:00
-- url     : https://prove2.me/submissions/9d5cb225-8c07-4014-b791-ef4a0e800e70

import Mathlib.Analysis.Complex.Basic

open scoped BigOperators

theorem solution (n : ℕ) (x : Fin n → ℝ) : ∑ i, ‖x i‖ ≥ ‖∑ i, x i‖ := by
  exact norm_sum_le Finset.univ x
