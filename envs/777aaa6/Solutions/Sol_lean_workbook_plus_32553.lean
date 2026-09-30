-- Prove2me | solution 1 for lean_workbook_plus_32553
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:23:16.126429+00:00
-- url     : https://prove2.me/submissions/0543cfcd-4951-4cc6-bb35-e2615fe809ad

import Mathlib

set_option autoImplicit false

theorem solution (a b m : Nat) (ha : 0 < a ∧ a < m)
    (hb : 0 < b ∧ b < m) (hab : (a : Int) ≡ (b : Int) [ZMOD (m : Int)]) : a = b := by
  have ha' : (a : Int) % m = a := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha.2)
  have hb' : (b : Int) % m = b := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb.2)
  have heq : (a : Int) = b := by simpa only [Int.ModEq, ha', hb'] using hab
  exact_mod_cast heq

#print axioms solution
