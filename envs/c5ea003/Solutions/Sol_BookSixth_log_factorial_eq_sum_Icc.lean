-- Prove2me | solution 1 for BookSixth.log_factorial_eq_sum_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:41:28.914606+00:00
-- url     : https://prove2.me/submissions/d3f67ad0-f11e-4a57-8327-7a38b3f9777b

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (r : Nat) :
    Real.log (r.factorial : Real)
      = ∑ k ∈ Finset.Icc 1 r, Real.log (k : Real) := by
  induction r with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : Nat) : Real) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have h2 : (0 : Real) < (n.factorial : Real) := by
      exact_mod_cast Nat.factorial_pos n
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul h1 (ne_of_gt h2), ih]
    rw [add_comm]; exact Eq.symm (Finset.sum_Icc_succ_top (f := fun k : Nat => Real.log (k : Real)) (by omega : 1 ≤ n + 1))
