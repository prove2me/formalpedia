-- Prove2me | solution 1 for WorkbookRestored.plus_14185
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:49.302107+00:00
-- url     : https://prove2.me/submissions/2a43bb76-00f9-4c67-bb11-5b389e69876c

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_14185. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : choose (2 * n) 2 = 2 * choose n 2 + n^2   := by
  induction n <;> simp [Nat.choose, *] <;> ring
#print axioms solution
