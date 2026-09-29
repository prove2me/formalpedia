-- Prove2me | solution 1 for ErdosProblems.Erdos269.exists_dyadicInternalPower_iff_log_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:21:57.400635+00:00
-- url     : https://prove2.me/submissions/291a66dc-d7b6-413c-ac70-21d1a94dcf3e

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Theorems.Thm_ErdosProblems_Erdos269_log_dyadic_succ_le
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case.  It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value.  The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators































/-! ## Finite pure-power jump enumeration -/

















/-! ## Single-coordinate jump ratios -/













/-! ## Finite jump grouping -/













/-! The first exact `{2,3,5}` kernel values. -/















/-! ## Exact short-shell multiplicity bounds -/













/-! ## Exact dyadic block geometry for `{2,3,5}` -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p) :
    (∃ e, DyadicInternalPower p a e) ↔
      Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) + 1 := by
  have hpOne : 1 < p := by omega
  constructor
  · rintro ⟨e, heLower, heUpper⟩
    have hLower : Nat.log p (2 ^ a) < e :=
      (Nat.log_lt_iff_lt_pow hpOne (by positivity)).2 heLower
    have hUpper : e ≤ Nat.log p (2 ^ (a + 1)) :=
      Nat.le_log_of_pow_le hpOne heUpper.le
    have hStep := log_dyadic_succ_le (a := a) (Nat.le_of_lt hp)
    omega
  · intro hStep
    let e := Nat.log p (2 ^ (a + 1))
    refine ⟨e, ?_, ?_⟩
    · dsimp [e]
      simpa only [Nat.succ_eq_add_one, hStep] using
        Nat.lt_pow_succ_log_self hpOne (2 ^ a)
    · dsimp [e]
      have hLe :
          p ^ Nat.log p (2 ^ (a + 1)) ≤ 2 ^ (a + 1) :=
        Nat.pow_log_le_self p (by positivity)
      have hOdd : Odd (p ^ Nat.log p (2 ^ (a + 1))) := hpOdd.pow
      have hEven : Even (2 ^ (a + 1)) :=
        even_two.pow_of_ne_zero (by omega)
      have hNe : p ^ Nat.log p (2 ^ (a + 1)) ≠ 2 ^ (a + 1) := by
        intro hEq
        exact (Nat.not_even_iff_odd.mpr hOdd) (by simpa [hEq] using hEven)
      exact lt_of_le_of_ne hLe hNe
