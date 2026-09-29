-- Prove2me | solution 1 for WorkbookRestored.plus_8968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:28.848986+00:00
-- url     : https://prove2.me/submissions/61e2bfbb-c92a-49e9-8805-1abe9023f18c

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_8968.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : choose 3 0 + choose 4 1 + choose 5 2 = choose 6 2   := by
  simp [Nat.choose_succ_succ, Nat.choose_symm_of_eq_add]
#print axioms solution
