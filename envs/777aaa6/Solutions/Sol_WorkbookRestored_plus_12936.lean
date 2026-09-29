-- Prove2me | solution 1 for WorkbookRestored.plus_12936
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:46.382478+00:00
-- url     : https://prove2.me/submissions/ac0c5b49-d768-4f9e-863b-6602fb655b4a

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_12936. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 2 ^ (Nat.totient 77) ≡ 1 [ZMOD 77]   := by
  decide +kernel
#print axioms solution
