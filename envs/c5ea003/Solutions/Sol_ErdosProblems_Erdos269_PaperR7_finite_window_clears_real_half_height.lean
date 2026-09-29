-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.finite_window_clears_real_half_height
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:43:01.711992+00:00
-- url     : https://prove2.me/submissions/470c7b72-6a24-4f67-b683-4d52a0f1df08

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
import Theorems.Thm_ErdosProblems_Erdos269_two_mul_heightNormalizer235
import Theorems.Thm_ErdosProblems_Erdos269_heightNormalizer235_mul_windowMass_eq_int
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
theorem solution (u b : ℕ) (hub : u ≤ b) :
    ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ) := by
  by_cases hb0 : b = 0
  · have hu0 : u = 0 := by omega
    subst b
    subst u
    exact ⟨0, by simp⟩
  · obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int u (b - u)
    have hidx : u + (b - u) = b := by omega
    rw [hidx] at hz
    have hpref : (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) =
        (dyadicSmoothWindowMassQ235 u (b - u) : ℝ) := by
      simp [dyadicSmoothWindowMassQ235, dyadicShellMassR235]
    have hh : (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 =
        (heightNormalizer235 b : ℝ) := by
      have h := two_mul_heightNormalizer235 b (by omega)
      have hR : 2 * (heightNormalizer235 b : ℝ) =
          (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) := by exact_mod_cast h
      linarith
    refine ⟨z, ?_⟩
    rw [hh, hpref]
    exact_mod_cast hz
