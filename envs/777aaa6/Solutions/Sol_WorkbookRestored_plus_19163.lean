-- Prove2me | solution 1 for WorkbookRestored.plus_19163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:53.434625+00:00
-- url     : https://prove2.me/submissions/9754e2cd-46da-4854-a107-27b25395b4e5

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_19163. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a t : ℝ) (ha : a > 0) (ht : t ≥ 0) : ∃ g : ℝ → ℝ, ∀ x > 0, g x = x ^ t ∧ g 0 = 0 ∧ ∀ x < 0, g x = -a * (-x) ^ t   := by
  refine ⟨fun x => if x = 0 then 0 else if x < 0 then -a * (-x) ^ t else x ^ t, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · simp [ne_of_gt hx, not_lt_of_ge (le_of_lt hx)]
  · simp
  · intro y hy
    simp [ne_of_lt hy, hy]
#print axioms solution
