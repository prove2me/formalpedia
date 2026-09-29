-- Prove2me | solution 1 for WorkbookRestored.plus_21774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:42.592985+00:00
-- url     : https://prove2.me/submissions/f7dc3749-859a-4122-964e-6baabf7328e1

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_21774.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1) →  (Real.log b / Real.log a) * (Real.log c / Real.log b) = (Real.log c / Real.log a)   := by
  rintro a b c ⟨ha, hb, hc, h₁, h₂, h₃⟩
  have ha' := Real.log_ne_zero_of_pos_of_ne_one ha h₁
  have hb' := Real.log_ne_zero_of_pos_of_ne_one hb h₂
  field_simp [ha', hb'] <;> ring
#print axioms solution
