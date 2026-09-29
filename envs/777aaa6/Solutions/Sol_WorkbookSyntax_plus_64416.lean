-- Prove2me | solution 1 for WorkbookSyntax.plus_64416
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:26:43.991003+00:00
-- url     : https://prove2.me/submissions/9cd899f8-bdb5-4ea5-ba8c-21da11d1017e

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (p : ℕ → ℕ) (hp : ∀ x, p x = ∑ i ∈ Finset.range 1008, Nat.choose x i) : p 2015 = 2^2014   := by
  rw [hp]
  calc
    _ = 4 ^ 1007 := by simpa using Nat.sum_range_choose_halfway 1007
    _ = 2 ^ 2014 := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
#print axioms solution
