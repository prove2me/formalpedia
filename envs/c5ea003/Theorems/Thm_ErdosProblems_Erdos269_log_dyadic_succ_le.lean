-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_log_dyadic_succ_le
-- name    : ErdosProblems.Erdos269.log_dyadic_succ_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:21:08.736455+00:00
-- url     : https://prove2.me/theorems/add16f71-876c-4c35-8c22-01fa5be633c9
-- title:
--   Log dyadic succ le
-- statement:
--   For every base p at least 2, its floor logarithm rises by at most one across one dyadic block.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L686-L697
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













/-! ## Exact dyadic block geometry for `{2,3,5}` -/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.log_dyadic_succ_le
    {p a : ℕ} (hp : 2 ≤ p) :
    Nat.log p (2 ^ (a + 1)) ≤ Nat.log p (2 ^ a) + 1 := by sorry
