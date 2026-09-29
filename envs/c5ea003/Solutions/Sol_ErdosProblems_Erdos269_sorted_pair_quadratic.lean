-- Prove2me | solution 1 for ErdosProblems.Erdos269.sorted_pair_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:01:55.223744+00:00
-- url     : https://prove2.me/submissions/7788e9fc-91a6-4084-8f89-122a4ccf819e

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
    {a b c j : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : a + b + c = j) :
    9 * ((a + 1) * (b + 1)) ≤ (j + 3) ^ 2 := by
  have hj : a + 2 * b ≤ j := by omega
  let d := b - a
  have hd : d + a = b := by
    dsimp [d]
    omega
  have hnon : 0 ≤ d * (3 * a + 4 * d + 3) := Nat.zero_le _
  have hlocal :
      9 * ((a + 1) * (b + 1)) ≤ (a + 2 * b + 3) ^ 2 := by
    nlinarith
  exact hlocal.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hj 3) 2)
