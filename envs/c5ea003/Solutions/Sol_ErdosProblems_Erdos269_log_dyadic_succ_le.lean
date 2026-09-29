-- Prove2me | solution 1 for ErdosProblems.Erdos269.log_dyadic_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:21:17.306495+00:00
-- url     : https://prove2.me/submissions/c12578e8-9090-46e9-809e-10f5415bf7c2

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













/-! ## Exact dyadic block geometry for `{2,3,5}` -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p a : ℕ} (hp : 2 ≤ p) :
    Nat.log p (2 ^ (a + 1)) ≤ Nat.log p (2 ^ a) + 1 := by
  calc
    Nat.log p (2 ^ (a + 1)) ≤ Nat.log p (2 ^ a * p) := by
      apply Nat.log_mono_right
      rw [pow_succ]
      exact Nat.mul_le_mul_left (2 ^ a) hp
    _ = Nat.log p (2 ^ a) + 1 := by
      exact Nat.log_mul_base (by omega) (by positivity)
