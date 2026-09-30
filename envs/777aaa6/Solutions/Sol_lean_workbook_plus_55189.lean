-- Prove2me | solution 1 for lean_workbook_plus_55189
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:42:42.292092+00:00
-- url     : https://prove2.me/submissions/ea0c288a-09e9-4b0c-b7ea-98985b4083ae

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ∀ n : ℕ, n > 4 → 2 ^ n > n ^ 2 := by
  intro n hn
  have hge : 5 ≤ n := by omega
  induction n, hge using Nat.le_induction with
  | base => norm_num
  | succ n hge ih =>
    specialize ih (by omega)
    rw [pow_succ]
    have hmul : 3 * n ≤ n * n := Nat.mul_le_mul_right n (by omega : 3 ≤ n)
    nlinarith

#print axioms solution
