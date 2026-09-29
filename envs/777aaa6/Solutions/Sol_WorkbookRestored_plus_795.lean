-- Prove2me | solution 1 for WorkbookRestored.plus_795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:59:03.410978+00:00
-- url     : https://prove2.me/submissions/9a751437-8a52-4ba6-9c62-3aababafe719

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_795.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (h : n ≠ 0) : Odd (choose n 1) → Odd n   := by
  intro hn
  simpa only [Nat.choose_one_right] using hn
#print axioms solution
