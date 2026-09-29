-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:18:46.127751+00:00
-- url     : https://prove2.me/theorems/a98c9c0d-4325-41b7-8754-efb2eb6f5601
-- title:
--   WeightedShiftArithmetic
-- statement:
--   Defines shifted endpoint heights, their ratio Γ, a weighted shifted numerator over integer coefficients, and a cleared finite prefix. Their integrality and bounds are separate theorems.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/WeightedShiftArithmetic.lean#L1-L144
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
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact arithmetic of the paper's weighted shifts

The ratio is defined from the actual dyadic heights. Integer logarithms
prove its four-element alphabet without numerical logarithms. The factor
15 clears both the shifted coefficients and the finite prefix correction.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators

abbrev shiftHeight (n : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ n)

noncomputable def shiftGamma (a t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ) / (shiftHeight (a + t + 1) : ℝ)











noncomputable def shiftedNumerator (c : ℕ → ℤ) (σ r a : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)





noncomputable def shiftedPrefix (t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * ∑ k ∈ Finset.range t,
    (dyadicOrderedBlockDigit235 k : ℝ) / (shiftHeight (k + 1) : ℝ)




end ErdosProblems.Erdos269.PaperCompleteR20


