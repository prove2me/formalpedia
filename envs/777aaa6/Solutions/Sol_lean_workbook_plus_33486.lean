-- Prove2me | solution 1 for lean_workbook_plus_33486
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:17:09.428723+00:00
-- url     : https://prove2.me/submissions/9c43e90d-eb20-49ba-915e-6090734cb6e9

import Mathlib

set_option autoImplicit false

theorem solution (n : Nat) (hn : 9 < n) : 2^n > n^3 := by
  have hge : 10 ≤ n := by omega
  induction n, hge using Nat.le_induction with
  | base => norm_num
  | succ n hge ih =>
    specialize ih (by omega)
    have hstep : (n+1)^3 ≤ 2*n^3 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
      nlinarith [Nat.zero_le (k^3)]
    rw [pow_succ]
    omega

#print axioms solution
