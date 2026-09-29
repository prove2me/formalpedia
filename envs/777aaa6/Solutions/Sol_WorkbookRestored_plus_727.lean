-- Prove2me | solution 1 for WorkbookRestored.plus_727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:22.215008+00:00
-- url     : https://prove2.me/submissions/e1c4c070-fd48-440b-803a-d3e0d2a653ed

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_727.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic
open Complex
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (hn : n ≠ 0) : ‖(1 : ℂ) ^ (1 / n : ℂ)‖ = 1   := by
  simp [hn, norm_one]
#print axioms solution
