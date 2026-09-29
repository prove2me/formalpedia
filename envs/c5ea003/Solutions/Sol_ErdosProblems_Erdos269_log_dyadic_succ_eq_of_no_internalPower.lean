-- Prove2me | solution 1 for ErdosProblems.Erdos269.log_dyadic_succ_eq_of_no_internalPower
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:22:42.59235+00:00
-- url     : https://prove2.me/submissions/784cee38-50d2-4a25-a098-15a2709e34c6

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Theorems.Thm_ErdosProblems_Erdos269_log_dyadic_succ_le
import Theorems.Thm_ErdosProblems_Erdos269_exists_dyadicInternalPower_iff_log_succ
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
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p)
    (hNo : ¬ ∃ e, DyadicInternalPower p a e) :
    Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) := by
  have hMono : Nat.log p (2 ^ a) ≤ Nat.log p (2 ^ (a + 1)) := by
    apply Nat.log_mono_right
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ a)
  have hStep := log_dyadic_succ_le (a := a) (by omega : 2 ≤ p)
  have hNotSucc :
      Nat.log p (2 ^ (a + 1)) ≠ Nat.log p (2 ^ a) + 1 := by
    intro hEq
    exact hNo ((exists_dyadicInternalPower_iff_log_succ hp hpOdd).2 hEq)
  omega
