-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.octic_escape_whole
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:12:06.203661+00:00
-- url     : https://prove2.me/submissions/8175f535-3de3-4ba7-952a-e4aab528a0f3

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Definitions.Def_ErdosProblems_Erdos269_SharpWindowCapR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_OcticEscapeWhole
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_quadratic_cap_div_eight_pow_tendsto
import Theorems.Thm_ErdosProblems_Erdos269_PaperR11_longPaperCap_le_three_squareR11
import Theorems.Thm_ErdosProblems_Erdos269_PaperR11_long_cap_window_equivalenceR11
import Theorems.Thm_ErdosProblems_Erdos269_PaperR12_octic_window_band
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_escape_zero_cap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

namespace PaperR7
end PaperR7

/-! Complete octic escape statement, including the hypotheses for both named
caps and the automatic zero-cap case. The irrationality target stays open. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open Filter PaperR7 PaperR11 PaperR12
open scoped Topology





theorem long_cap_le_shortPaperCap (B a : ℕ) : longPaperCap B a ≤ shortPaperCap B a := by
  apply (longPaperCap_le_three_squareR11 B a).trans
  exact Nat.mul_le_mul_right ((a + 1) ^ 2)
    (Nat.mul_le_mul_right B (by decide : 3 ≤ 90))

theorem long_cap_div_eight_pow_tendsto (B : ℕ) :
    Tendsto (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (quadratic_cap_div_eight_pow_tendsto (3 * B))
    (Eventually.of_forall fun a => ?_) (Eventually.of_forall fun a => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast longPaperCap_le_three_squareR11 B a

theorem short_cap_div_eight_pow_tendsto (B : ℕ) :
    Tendsto (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a)
      atTop (𝓝 0) := quadratic_cap_div_eight_pow_tendsto (90 * B)
end ErdosProblems.Erdos269.PaperCompleteR20

open Filter PaperR7 PaperR11 PaperR12
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR11 in
open ErdosProblems.Erdos269.PaperR12 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B →
        Tendsto (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational paperSeries235)) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational paperSeries235) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational paperSeries235) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by
  refine ⟨octic_window_band, long_cap_div_eight_pow_tendsto,
    long_cap_le_shortPaperCap, short_cap_div_eight_pow_tendsto,
    long_cap_window_equivalenceR11, ?_, escape_zero_cap⟩
  exact octic_window_band shortPaperCap (fun B a _ => long_cap_le_shortPaperCap B a)
    (fun B _ => short_cap_div_eight_pow_tendsto B)
