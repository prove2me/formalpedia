-- Prove2me | solution 1 for BookSixth.log_factorial_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:54:55.637866+00:00
-- url     : https://prove2.me/submissions/931f1af6-4230-453b-b3d3-9f30dfb6ffd9

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (r : Nat) :
    (∑ k ∈ Finset.Icc 1 r, Real.log (k : Real)) / (r : Real)
      = Real.log (r.factorial : Real) / (r : Real) := by
  have key : ∀ s : Nat, ∑ k ∈ Finset.Icc 1 s, Real.log (k : Real)
      = Real.log (s.factorial : Real) := by
    intro s
    induction s with
    | zero => simp
    | succ n ih =>
      have h1 : ((n + 1 : Nat) : Real) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have h2 : (0 : Real) < (n.factorial : Real) := by
        exact_mod_cast Nat.factorial_pos n
      have hmem : (1 : Nat) ≤ n + 1 := by omega
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul h1 (ne_of_gt h2),
        Finset.sum_Icc_succ_top (f := fun k : Nat => Real.log (k : Real)) hmem,
        ih, add_comm]
  rw [key r]
