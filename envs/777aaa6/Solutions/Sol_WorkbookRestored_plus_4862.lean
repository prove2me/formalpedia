-- Prove2me | solution 1 for WorkbookRestored.plus_4862
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:26.190002+00:00
-- url     : https://prove2.me/submissions/dfe2850c-b0e7-4189-a269-6afd76001881

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_4862.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n m : ℕ) : choose n m + choose n (m + 1) = choose (n + 1) (m + 1)   := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
#print axioms solution
