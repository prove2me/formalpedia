-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_pos
-- name    : ErdosProblems.Erdos269.dyadicShellMassR235_pos
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:14:46.768871+00:00
-- url     : https://prove2.me/theorems/d4a576cd-c488-4eb6-8ac1-fb610ab3a384
-- title:
--   DyadicShellMassR235 pos
-- statement:
--   The real dyadic shell mass is positive.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/IntegralBranchExtinction.lean#L78-L80
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
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


open scoped BigOperators

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.dyadicShellMassR235_pos (a : ℕ) : 0 < dyadicShellMassR235 a := by sorry
