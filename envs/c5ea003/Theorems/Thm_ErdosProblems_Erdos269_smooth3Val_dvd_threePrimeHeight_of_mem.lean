-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_smooth3Val_dvd_threePrimeHeight_of_mem
-- name    : ErdosProblems.Erdos269.smooth3Val_dvd_threePrimeHeight_of_mem
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:02:42.555815+00:00
-- url     : https://prove2.me/theorems/cd2e4aba-f040-4ca4-a755-9dd7c0334ff3
-- title:
--   Smooth3Val dvd threePrimeHeight of mem
-- statement:
--   Every smooth prefix value divides the coordinatewise running height at its cutoff.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L58-L75
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

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.smooth3Val_dvd_threePrimeHeight_of_mem
    {p q r x : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ smoothPrefixExponents p q r x) :
    smooth3Val p q r e.1 e.2.1 e.2.2 ∣ threePrimeHeight p q r x := by sorry
