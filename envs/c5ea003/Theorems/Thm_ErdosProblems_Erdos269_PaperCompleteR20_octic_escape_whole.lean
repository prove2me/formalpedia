-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_octic_escape_whole
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.octic_escape_whole
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:10:43.69575+00:00
-- url     : https://prove2.me/theorems/8f9cdb1b-5d85-41a1-b301-89becdb471a4
-- title:
--   Octic escape whole
-- statement:
--   For the 2·3·5 series, let G(B,a) be a natural-valued cap such that, for every positive B, G(B,a) dominates the long paper cap for all a and G(B,a)/8^a tends to zero. Then cofinal local-window escape for G is equivalent to irrationality of the series. The long and short paper caps have this decay, the long cap is at most the short cap, and each gives the equivalence. Separately, the zero cap has cofinal escape; it does not meet the domination premise that would imply irrationality.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/OcticEscapeWhole.lean#L49-L71
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


open Filter PaperR7 PaperR11 PaperR12
open scoped Topology

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR11
open ErdosProblems.Erdos269.PaperR12
open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperCompleteR20.octic_escape_whole :
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
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by sorry
