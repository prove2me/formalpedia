-- Prove2me | solution 1 for ErdosProblems.Erdos269.threePrimeHeight_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:30:44.369391+00:00
-- url     : https://prove2.me/submissions/039c2de8-dbd3-4401-af4c-fd6389c88673

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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (p q r x : ℕ) (hx : x ≠ 0) :
    threePrimeHeight p q r x ≤ x ^ 3 := by
  have hp := Nat.pow_log_le_self p hx
  have hq := Nat.pow_log_le_self q hx
  have hr := Nat.pow_log_le_self r hx
  calc
    threePrimeHeight p q r x
        ≤ (x * x) * x := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
    _ = x ^ 3 := by ring
