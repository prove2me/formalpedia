-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR7_dyadic_height_le_eight_pow
-- name    : ErdosProblems.Erdos269.PaperR7.dyadic_height_le_eight_pow
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:04:25.339677+00:00
-- url     : https://prove2.me/theorems/e4bdb114-582d-4491-a3ca-5f315363f96e
-- title:
--   Dyadic height le eight pow
-- statement:
--   The three-prime height at dyadic scale a is at most 8^a.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7SharpShellBound.lean#L83-L88
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
import Mathlib.Analysis.SpecificLimits.Normed
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

namespace ErdosProblems.Erdos269.PaperR7
end ErdosProblems.Erdos269.PaperR7

/-!
# Round 7: the literal `8640 / 343` shell bound

Target: the bound in short-note `res:actual-orbit`.  The supplied bound `90`
does not prove this sharper displayed constant.  We retain the actual shell
mass, prove its `8^{-a}` estimate, and sum the resulting majorant exactly.
This is NOT a proof of the separate long-record `Q(n_a)` bound.

No admissions.
-/


open scoped BigOperators

open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperR7.dyadic_height_le_eight_pow (a : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) ≤ (8 : ℝ) ^ a := by sorry
