-- Prove2me | solution 1 for WorkbookRestored.plus_68777
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:10.520984+00:00
-- url     : https://prove2.me/submissions/56f87721-fb24-44d1-9dc2-0ac50f538fcc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_68777.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  Nat.totient 462 = 120   := by
  decide +kernel
#print axioms solution
