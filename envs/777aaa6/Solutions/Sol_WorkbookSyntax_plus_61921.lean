-- Prove2me | solution 1 for WorkbookSyntax.plus_61921
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:26:43.102873+00:00
-- url     : https://prove2.me/submissions/9a66bf1c-ea44-46b6-bcc0-8eacd2393965

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (n : ℕ) : ∑ k ∈ Finset.range (n+1), fib k ^ 2 = fib n * fib (n + 1)   := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_eq_add_one, show n + 1 + 1 = n + 2 by omega, Nat.fib_add_two]
    ring
#print axioms solution
