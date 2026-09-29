-- Prove2me | solution 1 for WorkbookRestored.plus_23528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:44.106515+00:00
-- url     : https://prove2.me/submissions/85fcee05-7833-4254-b9ce-e191a7e0c733

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_23528.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  Real.log x < x - 1 ∧ x - 1 < (x - 1) / (2 - x)   := by
  have h1 : 0 < x ∧ x < 1 := hx
  have h2 := log_lt_sub_one_of_pos h1.1
  have h3 : 0 < 2 - x := by linarith
  have h4 : x - 1 < (x - 1) / (2 - x) := by
    rw [div_eq_mul_inv]
    ring_nf
    rw [← sub_pos]
    field_simp [h1.1, h1.2, h3]
    nlinarith [h1.1, h1.2]
  exact ⟨h2 (ne_of_lt h1.2), h4⟩
#print axioms solution
