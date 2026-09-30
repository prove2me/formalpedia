-- Prove2me | solution 1 for lean_workbook_plus_29310
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:06.450127+00:00
-- url     : https://prove2.me/submissions/7760316e-3226-4083-b809-caa938078f0a

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) : (2 * n).choose 2 = 2 * n.choose 2 + n ^ 2   := by
  have hstep (k : ℕ) : (k + 1).choose 2 = k + k.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ k 1
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      hstep (2 * n + 1), hstep (2 * n), ih, hstep n]
    ring

#print axioms solution
