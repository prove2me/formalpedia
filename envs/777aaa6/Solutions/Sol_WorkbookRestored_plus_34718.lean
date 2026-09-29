-- Prove2me | solution 1 for WorkbookRestored.plus_34718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:09.131707+00:00
-- url     : https://prove2.me/submissions/9b1e7c7b-d305-440f-9a38-6dbc7ad17821

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34718.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (q e : ℂ)
  (h₀ : q = Complex.I)
  (h₁ : e = 4) :
  q^e = 1   := by
  simp [h₀, h₁, Complex.I_sq, Complex.ext_iff]
#print axioms solution
