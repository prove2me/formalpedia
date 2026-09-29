-- Prove2me | solution 1 for ErdosProblems.Erdos269.exponent_unique_in_short_interval
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:20:52.363024+00:00
-- url     : https://prove2.me/submissions/175462a7-1e3a-4b62-9c2c-d0e157d28810

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {base lo hi weight a b : ℕ}
    (hbase : 0 < base) (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpow : base ^ (a + 1) ≤ base ^ b :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ a * weight) := Nat.mul_le_mul_left base haLo
      _ = base ^ (a + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ b * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := hbHi
    exact (Nat.lt_irrefl hi hcontra).elim
  · exact hab
  · have hpow : base ^ (b + 1) ≤ base ^ a :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ b * weight) := Nat.mul_le_mul_left base hbLo
      _ = base ^ (b + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ a * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := haHi
    exact (Nat.lt_irrefl hi hcontra).elim
