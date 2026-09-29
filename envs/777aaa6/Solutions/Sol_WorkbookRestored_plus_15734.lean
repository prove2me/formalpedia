-- Prove2me | solution 1 for WorkbookRestored.plus_15734
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:51.827728+00:00
-- url     : https://prove2.me/submissions/ba121c2c-d853-445c-8f00-58d960aecf83

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_15734. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : (Nat.digits 10 n).sum % 9 = n % 9   := by
  exact (Nat.modEq_digits_sum 9 10 (by norm_num) n).symm
#print axioms solution
