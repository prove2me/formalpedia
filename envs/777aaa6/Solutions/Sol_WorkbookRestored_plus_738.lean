-- Prove2me | solution 1 for WorkbookRestored.plus_738
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:39.525242+00:00
-- url     : https://prove2.me/submissions/f1d7ebfe-aef5-4042-9465-0fa1af26b3c1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_738.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (r : ℝ)
  (h₀ : Real.log 5 = r * Real.log 2) :
  r = Real.logb 2 5   := by
  rw [Real.logb]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact (eq_div_iff h2).2 h₀.symm
#print axioms solution
