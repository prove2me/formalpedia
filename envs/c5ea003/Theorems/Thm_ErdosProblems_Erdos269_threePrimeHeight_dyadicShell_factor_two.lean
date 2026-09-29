-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_dyadicShell_factor_two
-- name    : ErdosProblems.Erdos269.threePrimeHeight_dyadicShell_factor_two
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:00:55.424842+00:00
-- url     : https://prove2.me/theorems/4c3b3304-90b8-446a-b281-edd6ff94770a
-- title:
--   ThreePrimeHeight dyadicShell factor two
-- statement:
--   For each actual 2·3·5 smooth point in a dyadic shell, the next-endpoint running height is twice its point height times its odd suffix.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicBlockMassIdentity.lean#L92-L127
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
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
# Erdős #269: exact dyadic block-mass normalization

The integer checker compresses the smooth numbers in a half-open dyadic shell
`[2^a, 2^(a+1))`.  After clearing by the height at the right endpoint, every
summand contains the terminal dyadic factor `2`.  Dividing that common factor
leaves a suffix product of the zero, one, or two internal odd-prime jumps.

This file kernel-checks the complete cell algebra used by the checker.  The
remaining source-specific step is to identify the cell cardinalities with the
appropriate `strictSmoothShell` filters for every `a`.
-/


open scoped BigOperators

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.threePrimeHeight_dyadicShell_factor_two
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      2 * oddHeightSuffix235 a e *
        threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by sorry
