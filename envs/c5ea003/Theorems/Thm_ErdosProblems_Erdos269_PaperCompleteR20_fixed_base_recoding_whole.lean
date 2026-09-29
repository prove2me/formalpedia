-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_fixed_base_recoding_whole
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:32:47.499247+00:00
-- url     : https://prove2.me/theorems/5f985036-92f7-47a4-b207-734ed0b2169a
-- title:
--   Fixed base recoding whole
-- statement:
--   The 2·3·5 paper series divided by two has absolutely summable recodings in bases 30 and 8. The base-30 coefficients are positive integers with an exponential lower bound; the base-8 coefficients are positive rational numbers with a stated power-of-15 denominator and quadratic upper bound. For every integer base q≥2, all dyadic heights divide q^n exactly when 30 divides q, and the recoded coefficients satisfy the stated lower bound.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/FixedBaseRecoding.lean#L157-L183
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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_FixedBaseRecoding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Module.FiniteDimension
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

-- `Summable.norm` (the alias of `summable_norm_iff`) no longer arrives transitively on Lean 4.30.0
-- / Mathlib c5ea0035, and dot notation no longer resolves it because `Summable` now unfolds to
-- `Exists`. Imported explicitly and applied by name below. Statements are unchanged.
namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# Direct fixed-base recoding of the actual series

The coefficient is the literal termwise rescaling of the actual ordered
digit. Base 30 retains integrality; base 8 retains the quadratic bound and
has denominators supported on 3 and 5. No echoing hypothesis is asserted.
-/


open PaperR7 PaperR8
open scoped BigOperators

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR7
open ErdosProblems.Erdos269.PaperR8

theorem ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a) := by sorry
