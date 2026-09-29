-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR12.octic_cap_is_exactly_beaten
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:09:33.253636+00:00
-- url     : https://prove2.me/submissions/f7fa254c-3e1f-439c-abec-d86c0c4faeb5

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
import Theorems.Thm_ErdosProblems_Erdos269_two_pow_le_windowBase235
import Theorems.Thm_ErdosProblems_Erdos269_windowBase235_pos
import Theorems.Thm_ErdosProblems_Erdos269_exists_len_quadratic_div_lt
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_long_window_growth
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

namespace ErdosProblems.Erdos269.PaperR12
end ErdosProblems.Erdos269.PaperR12

namespace PaperR10
end PaperR10

namespace PaperR11
end PaperR11

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# Enlarged equivalence band: little-o(8^a), rather than little-o(2^a)

For the actual 2,3,5 height word, 8^len/15 < W. Keeping this exact scale
strictly enlarges the sufficient decay condition in the long paper. The
carry-dominating lower bound is still required. No irrationality producer
is assumed or proved unconditionally. A source-current public Wave A audit checked
the named declarations with only the permitted axioms; see
`verification/erdos269-wavea-validation.json`. A later comment-only edit requires
the same focused audit to refresh its byte-level source binding.
-/

namespace ErdosProblems.Erdos269.PaperR12
open PaperR7 PaperR8 PaperR10 PaperR11 Filter
open scoped Topology
end ErdosProblems.Erdos269.PaperR12

open PaperR7 PaperR8 PaperR10 PaperR11 Filter
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR12 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (G : ℕ → ℕ → ℕ)
    (hsmall : ∀ B, 0 < B →
      Tendsto (fun n : ℕ => (G B n : ℝ) / (8 : ℝ) ^ n) atTop (𝓝 0)) :
    ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ len : ℕ, 0 < len ∧
        ((max (G B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ) /
          (actualWindowBase lo len : ℝ) < ε := by
  intro B lo hB ε hε
  have hlo : 0 < (8 : ℝ) ^ lo := by positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      (G B n : ℝ) / (8 : ℝ) ^ n < ε / (15 * (8 : ℝ) ^ lo) :=
    (tendsto_order.1 (hsmall B hB)).2 _ (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨k, hk, hquad⟩ := exists_len_quadratic_div_lt (B * 90) (lo + N) hε
  have hlen : 0 < N + k := by omega
  have h8 : 0 < (8 : ℝ) ^ (N + k) := by positivity
  have h2 : 0 < (2 : ℝ) ^ k := by positivity
  have hW : (0 : ℝ) < (actualWindowBase lo (N + k) : ℝ) := by
    exact_mod_cast windowBase235_pos lo (N + k)
  have hW8 := (long_window_growth lo (N + k) (by omega)).2.1
  have hgshift : (G B (lo + (N + k)) : ℝ) / (8 : ℝ) ^ (N + k) < ε / 15 := by
    calc
      _ = (8 : ℝ) ^ lo *
          ((G B (lo + (N + k)) : ℝ) / (8 : ℝ) ^ (lo + (N + k))) := by
        rw [pow_add (8 : ℝ) lo (N + k)]
        field_simp
      _ < (8 : ℝ) ^ lo * (ε / (15 * (8 : ℝ) ^ lo)) :=
        mul_lt_mul_of_pos_left (hN _ (by omega)) hlo
      _ = ε / 15 := by field_simp
  have hg : (G B (lo + (N + k)) : ℝ) <
      ε * (actualWindowBase lo (N + k) : ℝ) := by
    have h1 := (div_lt_iff₀ h8).1 hgshift
    have h2 := mul_lt_mul_of_pos_left hW8 hε
    nlinarith only [h1, h2]
  have hden : (2 : ℝ) ^ k ≤ (actualWindowBase lo (N + k) : ℝ) := by
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (N + k) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (by omega : k ≤ N + k)
    have hbase : (2 : ℝ) ^ (N + k) ≤ (actualWindowBase lo (N + k) : ℝ) := by
      exact_mod_cast two_pow_le_windowBase235 lo (N + k)
    exact hpow.trans hbase
  have hb : ((B * bridgeWidth (lo + (N + k)) : ℕ) : ℝ) <
      ε * (actualWindowBase lo (N + k) : ℝ) := by
    calc
      _ = ((B * 90 * ((lo + N) + k + 1) ^ 2 : ℕ) : ℝ) := by
        unfold bridgeWidth
        push_cast
        ring
      _ < ε * (2 : ℝ) ^ k := (div_lt_iff₀ h2).1 hquad
      _ ≤ ε * (actualWindowBase lo (N + k) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hε.le
  refine ⟨N + k, hlen, (div_lt_iff₀ hW).2 ?_⟩
  rw [Nat.cast_max]
  exact max_lt_iff.2 ⟨hg, hb⟩
