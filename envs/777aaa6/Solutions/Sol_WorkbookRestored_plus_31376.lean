-- Prove2me | solution 1 for WorkbookRestored.plus_31376
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:35.468823+00:00
-- url     : https://prove2.me/submissions/393f8f18-004c-4b8b-9dc9-022ac4dc0c10

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_31376.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution x y : cos (arcsin x) - Real.sqrt (1 - x ^ 2) = cos (arcsin y) - Real.sqrt (1 - y ^ 2)   := by
  simp [Real.cos_arcsin]
#print axioms solution
