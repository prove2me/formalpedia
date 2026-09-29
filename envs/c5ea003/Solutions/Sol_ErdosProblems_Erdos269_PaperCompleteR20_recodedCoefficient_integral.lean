-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.recodedCoefficient_integral
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:00:44.706797+00:00
-- url     : https://prove2.me/submissions/14a15dd0-d52a-4750-8e1c-15eaa375a5c2

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_all_dyadic_heights_dvd_base_powers_iff
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_orderedDigit235_pos
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

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7 PaperR8
open scoped BigOperators









theorem recodedCoefficient_pos {q : ℕ} (hq : 0 < q) (a : ℕ) :
    0 < recodedCoefficient q a := by
  have hm : (0 : ℝ) < dyadicOrderedBlockDigit235 a := by exact_mod_cast orderedDigit235_pos a
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  exact div_pos (mul_pos hm (pow_pos hqR _)) (threePrimeHeight235_cast_pos _)
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR8
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution {q : ℕ} (hq : 0 < q) (h30 : 30 ∣ q) (a : ℕ) :
    ∃ z : ℕ, 0 < z ∧ recodedCoefficient q a = (z : ℝ) := by
  obtain ⟨k, hk⟩ := (all_dyadic_heights_dvd_base_powers_iff q).2 h30 (a + 1) (by omega)
  have hp : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) ≠ 0 :=
    (threePrimeHeight235_cast_pos _).ne'
  have hkR : (q : ℝ) ^ (a + 1) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have he : recodedCoefficient q a = ((dyadicOrderedBlockDigit235 a * k : ℕ) : ℝ) := by
    unfold recodedCoefficient
    rw [hkR]
    push_cast
    field_simp
  refine ⟨dyadicOrderedBlockDigit235 a * k, ?_, he⟩
  have hz := recodedCoefficient_pos hq a
  rw [he] at hz
  exact_mod_cast hz
