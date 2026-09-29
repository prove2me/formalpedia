-- Prove2me | solution 1 for ErdosProblems.Erdos269.trueNormalizedState_pinning_mul
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:13:45.806362+00:00
-- url     : https://prove2.me/submissions/2b57c3a7-af28-427f-bffa-be82ceeee8ea

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_dyadicBlockBase235_cases
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_dyadicBlock_succ
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellTsumTailR235_eq_shell_add
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: extinction of the integral branch through pinning windows

The bounded-radix dichotomy leaves exactly one branch between the genuine
infinite tail and cofinal escape: an exact integral normalized state.  This
module lands the structural facts that turn that branch into a decidable,
computationally mapped object.

## 1. Positivity and the pinning identity

Every genuine tail is strictly positive (each shell contains `2^a`).
Unrolling the shell decomposition gives the exact pinning identity

`X_a = d_a / b_a + X_(a+1) / b_a`,

so every true state lies strictly above its window anchor `d_a / b_a`.
In particular, when `b_a` divides `d_a`, the anchor is already an integer
and integrality would force `X_(a+1) = 0`, which positivity forbids: such
scales are killed outright.

## 2. Upward closure

The recurrence has integer coefficients, so one integral state makes every
later state integral.  The integral-index set is empty or a final segment,
so the whole question concentrates on a first integral index.

## 3. Iterated pinning and forced equality

Iterating the pinning identity expresses every true state as a finite
digit sum plus a remainder that carries another factor `2^-k` per shell
(because every block radix is at least two).  Any real orbit following the
recurrence from index `A` onward inside windows of a width function that
reproduces under the recurrence and vanishes against `2^-k` therefore
satisfies `|y_A - X_A| <= width (A+k) / 2^k -> 0`, hence equals the true
state.  Consequently an integer seed surviving all windows forever forces
the true state itself to be integral - exactly the quantity the companion
experiment `check_erdos269_integral_branch.py` measures.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators





theorem dyadicBlockBase235_pos (a : ℕ) : 0 < dyadicBlockBase235 a := by
  rcases dyadicBlockBase235_cases a with h | h | h | h <;>
    simp [h]
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    trueNormalizedState a * (dyadicBlockBase235 a : ℝ)
      = (dyadicOrderedBlockDigit235 a : ℝ)
        + trueNormalizedState (a + 1) := by
  have hbpos : (0 : ℝ) < (dyadicBlockBase235 a : ℝ) := by
    exact_mod_cast dyadicBlockBase235_pos a
  have hsucc : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)
      = (dyadicBlockBase235 a : ℝ) * (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) :=
    mod_cast threePrimeHeight_dyadicBlock_succ a
  have hdigit : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
      * dyadicShellMassR235 a = (dyadicOrderedBlockDigit235 a : ℝ) :=
    half_threePrimeHeight_mul_dyadicShellMassR235 a
  have hsplit : dyadicShellTsumTailR235 a =
      dyadicShellMassR235 a + dyadicShellTsumTailR235 (a + 1) :=
    dyadicShellTsumTailR235_eq_shell_add a
  have hstate : trueNormalizedState (a + 1)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1) := rfl
  have hself : trueNormalizedState a
      = (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellTsumTailR235 a := rfl
  -- the future-tail share transfers through the radix product
  have hshare : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1)
          * (dyadicBlockBase235 a : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellTsumTailR235 (a + 1) := by
    rw [hsucc]
    ring
  have hmass : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2
        * dyadicShellMassR235 a * (dyadicBlockBase235 a : ℝ)
      = (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2
        * dyadicShellMassR235 a := by
    rw [hsucc]
    ring
  rw [hself, hstate, hsplit]
  linarith [hdigit, hshare, hmass]
