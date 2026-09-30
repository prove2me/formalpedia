-- Prove2me | solution 1 for lean_workbook_plus_34285
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:59:05.185766+00:00
-- url     : https://prove2.me/submissions/67352268-e2aa-44ed-9016-e740b1e87d72

import Mathlib.Data.Nat.Choose.Basic

theorem solution : ∀ n m : ℕ,
    n.factorial * m.factorial ∣ (n + m).factorial := by
  intro n m
  refine ⟨(n + m).choose m, ?_⟩
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.add_choose_mul_factorial_mul_factorial n m).symm

#print axioms solution
