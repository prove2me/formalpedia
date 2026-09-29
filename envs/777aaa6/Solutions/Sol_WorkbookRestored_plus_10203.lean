-- Prove2me | solution 1 for WorkbookRestored.plus_10203
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:31.42598+00:00
-- url     : https://prove2.me/submissions/88fa6ca2-5f36-4d6d-b0a2-dc2360457ffc

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_10203.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (r : ℕ) : choose (r + 1) 2 + choose (r + 1) 3 = choose (r + 2) 3   := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
#print axioms solution
