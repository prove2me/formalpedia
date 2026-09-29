-- Prove2me | Theorems.Thm_two_cycle_type_card_eq_factorial_ratio
-- name    : two_cycle_type_card_eq_factorial_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T03:12:29.645076+00:00
-- url     : https://prove2.me/theorems/9e60741c-4beb-4404-b5b0-ca358800aaa0
-- statement:
--   The number of permutations of $2n$ labelled elements whose cycle type is $n$ disjoint $2$-cycles is
--   $$
--   \#\{\sigma\in S_{2n}:\operatorname{cycleType}(\sigma)=2^n\}=\frac{(2n)!}{2^n n!}.
--   $$
--   This is the direct specialization of Mathlib's `Equiv.Perm.card_of_cycleType` formula to the multiset with $n$ copies of $2$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Real.Basic

theorem two_cycle_type_card_eq_factorial_ratio (n : Nat) :
    (({g | g.cycleType = Multiset.replicate n 2} :
        Finset (Equiv.Perm (Fin (2 * n)))).card : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) := by
  sorry
