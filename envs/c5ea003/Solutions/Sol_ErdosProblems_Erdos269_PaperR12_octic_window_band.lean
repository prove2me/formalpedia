-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR12.octic_window_band
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:10:59.515053+00:00
-- url     : https://prove2.me/submissions/cc27996a-79b6-42d7-81e8-46e91f1045b0

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_irrational_of_escape_dominating_sharp_cap
import Theorems.Thm_ErdosProblems_Erdos269_PaperR11_sharpPaperCap_le_longR11
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_irrational_tail_one_of_paperSeries
import Theorems.Thm_ErdosProblems_Erdos269_PaperR12_escape_of_irrational_of_exact_beating
import Theorems.Thm_ErdosProblems_Erdos269_PaperR12_octic_cap_is_exactly_beaten
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
open ErdosProblems.Erdos269.PaperR11 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (G : ℕ → ℕ → ℕ)
    (hdom : ∀ B a, 0 < B → longPaperCap B a ≤ G B a)
    (hsmall : ∀ B, 0 < B →
      Tendsto (fun n : ℕ => (G B n : ℝ) / (8 : ℝ) ^ n) atTop (𝓝 0)) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
      Irrational paperSeries235 := by
  constructor
  · exact irrational_of_escape_dominating_sharp_cap G
      (fun B a hB => (sharpPaperCap_le_longR11 B a).trans (hdom B a hB))
  · intro h
    exact escape_of_irrational_of_exact_beating
      (irrational_tail_one_of_paperSeries h) G (octic_cap_is_exactly_beaten G hsmall)
