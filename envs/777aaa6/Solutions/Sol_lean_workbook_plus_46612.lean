-- Prove2me | solution 1 for lean_workbook_plus_46612
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:49.21389+00:00
-- url     : https://prove2.me/submissions/17f93419-856e-4b43-99d5-9956774c0f41

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution {p : ℕ} (hp : Nat.Prime p) :
    Nat.factorial (2 * p) / Nat.factorial p ^ 2 = Nat.choose (2 * p) p := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega),
    show 2 * p - p = p by omega, pow_two]

#print axioms solution
