-- Prove2me | solution 1 for WorkbookSyntax.plus_70357
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:03.539996+00:00
-- url     : https://prove2.me/submissions/339f866f-5255-4b1b-9f33-3900b6fd1d39

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_70357.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (z : ℂ) : ∑ r ∈ Finset.range (n + 1), choose n r * z ^ r = (1 + z) ^ n   := by
  simpa [add_comm, mul_comm] using (add_pow z (1 : ℂ) n).symm
#print axioms solution
