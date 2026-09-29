-- Prove2me | solution 1 for lean_workbook_plus_10531
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:11.880178+00:00
-- url     : https://prove2.me/submissions/1fe02c20-f011-41dc-9e27-ad16e37de3bf

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (n i : ℕ) : (n.choose i) ^ 2 = n.choose i * n.choose (n - i) := by
  by_cases hi : i ≤ n
  · rw [Nat.choose_symm hi, pow_two]
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hi)]
    simp
