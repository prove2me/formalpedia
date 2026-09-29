-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_sorted_pair_quadratic
-- name    : ErdosProblems.Erdos269.sorted_pair_quadratic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:01:45.626559+00:00
-- url     : https://prove2.me/theorems/afa9fe6a-cce0-4f5a-8a44-f7f7b537d503
-- title:
--   Sorted pair quadratic
-- statement:
--   If a≤b≤c and a+b+c=j, then 9(a+1)(b+1)≤(j+3)^2.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L626-L643
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

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


open scoped BigOperators































/-! ## Finite pure-power jump enumeration -/

















/-! ## Single-coordinate jump ratios -/













/-! ## Finite jump grouping -/













/-! The first exact `{2,3,5}` kernel values. -/















/-! ## Exact short-shell multiplicity bounds -/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.sorted_pair_quadratic
    {a b c j : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : a + b + c = j) :
    9 * ((a + 1) * (b + 1)) ≤ (j + 3) ^ 2 := by sorry
