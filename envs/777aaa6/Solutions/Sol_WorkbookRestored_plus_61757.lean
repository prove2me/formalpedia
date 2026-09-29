-- Prove2me | solution 1 for WorkbookRestored.plus_61757
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:09.276056+00:00
-- url     : https://prove2.me/submissions/a392c593-abc4-4c9b-a1d5-7ea0db1b264e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_61757.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, exp x < 1 ∧ 1 < 1 / (1 + x) ∧ ∀ x ∈ Set.Ioi 0, exp x > 1 ∧ 1 > 1 / (1 + x)   := by
  intro x hx
  rcases hx with ⟨hx1,hx2⟩
  refine ⟨exp_lt_one_iff.2 hx2,?_,?_⟩
  · rw [lt_div_iff₀ (by linarith : (0:ℝ)<1+x)]
    linarith
  · intro y hy
    change 0 < y at hy
    refine ⟨one_lt_exp_iff.2 hy,?_⟩
    change 1/(1+y) < 1
    rw [div_lt_iff₀ (by linarith : (0:ℝ)<1+y)]
    linarith
#print axioms solution
