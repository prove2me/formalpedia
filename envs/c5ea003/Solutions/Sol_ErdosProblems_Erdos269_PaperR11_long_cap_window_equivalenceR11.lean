-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR11.long_cap_window_equivalenceR11
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:56:55.642992+00:00
-- url     : https://prove2.me/submissions/df988001-5621-45c9-a79f-192c0b165637

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR11_longPaperCap_le_three_squareR11
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_irrational_of_escape_dominating_sharp_cap
import Theorems.Thm_ErdosProblems_Erdos269_PaperR11_sharpPaperCap_le_longR11
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_irrational_tail_one_of_paperSeries
import Theorems.Thm_ErdosProblems_Erdos269_cofinalLocalWindowEscape_of_irrational_of_quadratic
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

namespace ErdosProblems.Erdos269.PaperR11
end ErdosProblems.Erdos269.PaperR11

namespace PaperR10
end PaperR10

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-! Narrow long-cap endpoint composition. No historical broad bridge import,
no missing producer, and no alteration of the onset or window conventions. -/

namespace ErdosProblems.Erdos269.PaperR11
open PaperR7 PaperR8 PaperR10
end ErdosProblems.Erdos269.PaperR11

open PaperR7 PaperR8 PaperR10
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR11 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational paperSeries235 := by
  constructor
  · exact irrational_of_escape_dominating_sharp_cap longPaperCap
      (fun B a _ => sharpPaperCap_le_longR11 B a)
  · intro h
    exact cofinalLocalWindowEscape_of_irrational_of_quadratic
      (irrational_tail_one_of_paperSeries h) longPaperCap (fun B => 3 * B)
      longPaperCap_le_three_squareR11
