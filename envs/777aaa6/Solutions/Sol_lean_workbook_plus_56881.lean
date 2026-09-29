-- Prove2me | solution 1 for lean_workbook_plus_56881
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:22:34.996451+00:00
-- url     : https://prove2.me/submissions/cd5ed6e6-4d57-4f73-8bf0-27b74a64f1e8

import Theorems.Thm_lean_workbook_plus_56881
import Mathlib.Tactic.NormNum

/-- Counterexample: `a = 2` gives `LHS = 2·(-1)/(-2) = 1 < 8 = 2·2² = RHS`. -/
theorem solution : ¬ lean_workbook_plus_56881 := by
  intro h
  have := h 2
  norm_num at this
