-- Prove2me | solution 1 for WorkbookRestored.plus_3121
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:23.03789+00:00
-- url     : https://prove2.me/submissions/4357bd29-8269-475a-a6fe-607d61ce5f21

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_3121.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : n * (n - 1) = 2 * choose n 2   := by
  simp [choose_two_right]
  rcases even_or_odd n with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> ring_nf
  all_goals omega
#print axioms solution
