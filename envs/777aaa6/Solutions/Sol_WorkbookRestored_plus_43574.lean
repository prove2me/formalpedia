-- Prove2me | solution 1 for WorkbookRestored.plus_43574
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:43.463882+00:00
-- url     : https://prove2.me/submissions/b887e2ba-903c-4258-8e9c-f3117794d305

/- InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_43574. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
theorem solution (I J : ℝ) (h₁ : I + J = 4) (h₂ : I - J = Real.pi) : I = (4 + Real.pi) / 2 ∧ J = (4 - Real.pi) / 2   := by
  exact ⟨by linarith [h₁, h₂], by linarith [h₁, h₂]⟩
#print axioms solution
