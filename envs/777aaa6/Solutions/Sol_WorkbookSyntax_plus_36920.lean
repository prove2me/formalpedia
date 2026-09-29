-- Prove2me | solution 1 for WorkbookSyntax.plus_36920
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:06.484711+00:00
-- url     : https://prove2.me/submissions/7fc1a3b5-0679-457c-8865-5e91bd171bed

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_36920.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  (∑ k ∈ (Nat.divisors 72), 1) = 12   := by
  decide +kernel
#print axioms solution
