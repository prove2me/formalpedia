-- Prove2me | solution 1 for WorkbookSyntax.plus_37758
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:07.245799+00:00
-- url     : https://prove2.me/submissions/d64e9b6f-f23b-4c1b-8efe-e6fc7061b62a

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_37758.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℕ → ℕ) (k : ℕ) :
  ∏ i ∈ Finset.range k, (x i)! ∣ (∑ i ∈ Finset.range k, x i)!   := by
  exact Nat.prod_factorial_dvd_factorial_sum (Finset.range k) x
#print axioms solution
