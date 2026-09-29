-- Prove2me | solution 1 for WorkbookRestored.plus_61458
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:40.434798+00:00
-- url     : https://prove2.me/submissions/7f5824eb-0ab0-4418-8e5e-3b80da7cacca

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_61458.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution {d n : ℕ} (h : d ∣ n) : totient d ∣ totient n   := by
  exact Nat.totient_dvd_of_dvd h
#print axioms solution
