-- Prove2me | solution 1 for lean_workbook_plus_4760
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:24.508538+00:00
-- url     : https://prove2.me/submissions/74627528-af0c-4c85-aa56-ea16eeddb3ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

theorem solution : ¬ IsClosed (Set.Ico (0 : ℝ) 1) := by
  intro h
  have hmem : (1 : ℝ) ∈ closure (Set.Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  rw [h.closure_eq] at hmem
  norm_num at hmem

#print axioms solution
