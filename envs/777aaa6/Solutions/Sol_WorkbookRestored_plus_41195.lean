-- Prove2me | solution 1 for WorkbookRestored.plus_41195
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:42.135046+00:00
-- url     : https://prove2.me/submissions/35d0ba3c-acbf-4204-9943-2621e38b0941

/- InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_41195. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
theorem solution (n m : ℕ) : Nat.gcd (Nat.fib n) (Nat.fib m) = Nat.fib (Nat.gcd n m)   := by
  cases n <;> cases m <;> simp [Nat.fib_gcd]
#print axioms solution
