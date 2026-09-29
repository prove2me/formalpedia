-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.long_all_scale_lattice
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:51:13.014629+00:00
-- url     : https://prove2.me/submissions/393d0f05-a8e2-4e9f-85b4-9e881c24eae4

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_finite_window_clears_real_half_height
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_tail_one_of_paperSeries_eq_rat
import Theorems.Thm_ErdosProblems_Erdos269_qsmul_normalizedTailState_eq_int_of_value_eq_rat
import Theorems.Thm_ErdosProblems_Erdos269_exists_normalizedTailState_collision_of_value_eq_rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Round 7: the fixed denominator split and the literal original value

The existing bridge existentially chooses a split and a carry. The paper fixes
`D = 2^u 3^v 5^w B`, fixes the onset, and identifies that carry with `B X_a`.
This file proves those equality data rather than citing a nearby existential.
The long-record sharper `Q`-cap remains a separate obligation.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution {N : ℤ} {D : ℕ} (hD : 0 < D)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
      (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
    (∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ ∃ z : ℤ,
      trueNormalizedState j - trueNormalizedState i = (z : ℝ)) := by
  have hq : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have ht : dyadicShellTsumTailR235 1 =
      ((N - (D : ℤ) : ℤ) : ℝ) / ((D : ℤ) : ℝ) := by
    simpa using tail_one_of_paperSeries_eq_rat hD hval
  refine ⟨finite_window_clears_real_half_height, ?_, ?_⟩
  · intro a ha
    simpa [trueNormalizedState] using qsmul_normalizedTailState_eq_int_of_value_eq_rat hq ht ha
  · obtain ⟨i, j, hij, z, hz⟩ := exists_normalizedTailState_collision_of_value_eq_rat hq ht
    exact ⟨1 + i, 1 + j, by omega, by omega, z, hz⟩
