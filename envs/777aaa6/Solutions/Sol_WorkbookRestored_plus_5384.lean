-- Prove2me | solution 1 for WorkbookRestored.plus_5384
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:27.004327+00:00
-- url     : https://prove2.me/submissions/422ce011-ff23-4659-b7a9-8a78f976d45f

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_5384.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∃ x : ℝ, x^2 = 2^x   := by
  refine' ⟨2, by norm_num⟩
#print axioms solution
