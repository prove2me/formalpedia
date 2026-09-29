-- Prove2me | solution 1 for WorkbookRestored.plus_14129
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:48.56859+00:00
-- url     : https://prove2.me/submissions/2c7523cd-5753-4fe8-a956-9b1ff3247e11

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_14129. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ k : ℕ, fib k + fib (k + 1) = fib (k + 2)   := by
  exact fun k ↦ by simp [fib_add_two]
#print axioms solution
