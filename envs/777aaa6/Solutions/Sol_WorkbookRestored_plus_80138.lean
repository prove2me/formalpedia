-- Prove2me | solution 1 for WorkbookRestored.plus_80138
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:33.519067+00:00
-- url     : https://prove2.me/submissions/9a9866f7-6606-45cb-85fa-c53969fc1d8b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80138.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x y : ℝ) :
  tan x * tan y * (tan x + tan y) / (tan x * tan y - 1) =
    (tan x ^ 2 * tan y + tan x * tan y ^ 2) / (tan x * tan y - 1)   := by
  ring
#print axioms solution
