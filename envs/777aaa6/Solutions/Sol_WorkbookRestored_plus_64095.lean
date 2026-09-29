-- Prove2me | solution 1 for WorkbookRestored.plus_64095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:11.488986+00:00
-- url     : https://prove2.me/submissions/f2ee3071-f040-4d0d-96c9-018d4bcd2621

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_64095.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y z u r a b c : ℝ) : 
  x = r * cos a * cos b * cos c ∧ 
  y = r * cos a * cos b * sin c ∧ 
  z = r * sin a * cos b ∧ 
  u = r * sin b → 
  x^2 + y^2 + z^2 + u^2 = r^2   := by
  rintro ⟨h₁, h₂, h₃, h₄⟩
  simp only [h₁, h₂, h₃, h₄, cos_sq, sin_sq, mul_pow, mul_add, mul_comm, mul_left_comm]
  ring
#print axioms solution
