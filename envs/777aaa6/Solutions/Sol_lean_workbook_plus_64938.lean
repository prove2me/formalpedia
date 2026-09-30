-- Prove2me | solution 1 for lean_workbook_plus_64938
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:37.470153+00:00
-- url     : https://prove2.me/submissions/419a92a7-1331-4741-8b76-25da763a65c2

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (hn : n ≠ 0) : 2 * (n * (n + 1) / 2) / (n * (n + 1) / 2) = 2   := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have hnum : 2 ≤ n * (n + 1) := by nlinarith
  have ht : 0 < n * (n + 1) / 2 := Nat.div_pos hnum (by decide)
  simpa only [Nat.mul_comm] using (Nat.mul_div_cancel_left 2 ht)

#print axioms solution
