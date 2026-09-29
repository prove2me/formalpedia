-- Prove2me | solution 1 for WorkbookRestored.plus_76059
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:48.840074+00:00
-- url     : https://prove2.me/submissions/61b8199f-1536-4355-bbc2-b77bbb2a7002

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_76059.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (b : ℝ) (hb : 1 < b) : Set.range (λ x : ℝ => b^x) = Set.Ioi 0   := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Real.rpow_pos_of_pos (zero_lt_one.trans hb) x
  · intro hy
    exact ⟨Real.logb b y, Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hy⟩
#print axioms solution
