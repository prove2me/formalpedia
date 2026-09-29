-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.short_fixed_split_bridge
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:35:43.654986+00:00
-- url     : https://prove2.me/submissions/1aa61b1d-3bf9-4678-9ba3-bf8f4ae14697

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_fixed_split_scaled_state_is_integer
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_scaled_actual_recurrence
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_mul_le
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_pos
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







theorem paperReducedCarry_cast {N : ℤ} {D u v w B a : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ))
    (ha : u + 1 + 2 * v + 3 * w ≤ a) :
    (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a := by
  obtain ⟨z, hz⟩ := fixed_split_scaled_state_is_integer hB hD hval ha
  unfold paperReducedCarry
  rw [hz, Int.floor_intCast]
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) := by
  intro a ha
  have hc := paperReducedCarry_cast hB hD hval ha
  have hcn := paperReducedCarry_cast hB hD hval (a := a + 1) (by omega)
  have hposR : (0 : ℝ) < (B : ℝ) * trueNormalizedState a :=
    mul_pos (by exact_mod_cast hB) (trueNormalizedState_pos a)
  have hpos : 0 < paperReducedCarry B a := by
    rw [← hc] at hposR
    exact_mod_cast hposR
  refine ⟨hc, hpos, ?_, ?_⟩
  · have hr := scaled_actual_recurrence (B : ℤ) a
    have heq : (paperReducedCarry B (a + 1) : ℝ) =
        (((dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) : ℤ) : ℝ) := by
      rw [hcn]
      push_cast at hr ⊢
      rw [hc]
      exact hr
    exact_mod_cast heq
  · have hu := trueNormalizedState_mul_le a (q := (B : ℝ)) (Nat.cast_nonneg _)
    rw [← hc] at hu
    have hbound : (paperReducedCarry B a : ℝ) ≤
        (((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) : ℝ) := by
      push_cast at hu ⊢
      nlinarith [hu]
    exact_mod_cast hbound
