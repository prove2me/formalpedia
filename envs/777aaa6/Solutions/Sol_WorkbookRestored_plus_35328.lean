-- Prove2me | solution 1 for WorkbookRestored.plus_35328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:10.75562+00:00
-- url     : https://prove2.me/submissions/1de345a9-313f-4079-9011-602fdacd9d9b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_35328.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (h₁ : π * 8^2 = 64 * π) : 1 / 2 * 12 * 28 - 1 / 2 * π * 8^2 = 168 - 32 * π   := by
  ring
#print axioms solution
