-- Prove2me | solution 1 for WorkbookSyntax.plus_67158
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:57.280986+00:00
-- url     : https://prove2.me/submissions/81ebc388-de76-4ba4-b325-658793e651e2

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_67158.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : (∏ i ∈ Finset.range 1000, (2 * i + 2)) - (∏ i ∈ Finset.range 1000, (2 * i + 1)) ≡ 0 [ZMOD 2001]   := by
  decide +kernel
#print axioms solution
