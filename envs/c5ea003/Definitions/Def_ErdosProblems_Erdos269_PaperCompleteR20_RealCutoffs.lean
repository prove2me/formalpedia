-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:16:31.754702+00:00
-- url     : https://prove2.me/theorems/13b024aa-f430-4a02-b194-2122e6e45b88
-- title:
--   RealCutoffs
-- statement:
--   Defines equality of three real floor-logarithm cells and a finite real smooth exponent shell with specified exponent bounds and a half-open value interval.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L1-L321
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

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open Finset
open scoped BigOperators

noncomputable section

open PaperR10





/-- Literal real logarithmic-cell relation from the paper. -/
def SameThreePrimeRealLogCell (p q r : ℕ) (x y : ℝ) : Prop :=
  ⌊Real.logb p x⌋₊ = ⌊Real.logb p y⌋₊ ∧
    ⌊Real.logb q x⌋₊ = ⌊Real.logb q y⌋₊ ∧
      ⌊Real.logb r x⌋₊ = ⌊Real.logb r y⌋₊























/-- Exponent triples in the paper's real half-open shell. -/
def realSmoothExponentShell
    (p q r : ℕ) (lo hi : ℝ) (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (hp + 1)).product
      ((range (hq + 1)).product (range (hr + 1)))).filter
    fun e => lo ≤ (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ∧
      (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) < hi








end
end ErdosProblems.Erdos269.PaperCompleteR20


