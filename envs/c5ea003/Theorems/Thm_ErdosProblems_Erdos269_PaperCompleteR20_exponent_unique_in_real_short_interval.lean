-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_exponent_unique_in_real_short_interval
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_in_real_short_interval
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:22:36.425204+00:00
-- url     : https://prove2.me/theorems/7089d762-2b83-4300-a229-881a8bc60a6a
-- title:
--   Exponent unique in real short interval
-- statement:
--   For positive natural base and nonnegative real weight, a real multiplicative interval [lo,hi) of width at most base admits at most one natural base exponent.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L163-L201
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
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
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

namespace PaperR10
end PaperR10

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/


open Finset
open scoped BigOperators

noncomputable section

open PaperR10

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR10

theorem ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_in_real_short_interval
    {base a b : ℕ} {lo hi weight : ℝ}
    (hbase : 0 < base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ (base : ℝ) * lo)
    (haLo : lo ≤ (base : ℝ) ^ a * weight)
    (haHi : (base : ℝ) ^ a * weight < hi)
    (hbLo : lo ≤ (base : ℝ) ^ b * weight)
    (hbHi : (base : ℝ) ^ b * weight < hi) :
    a = b := by sorry
