-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.all_dyadic_heights_dvd_base_powers_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:00:05.535526+00:00
-- url     : https://prove2.me/submissions/a0d9efe4-ac9d-4390-bcfa-461bde9e9d33

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR8_sorted_height_profile
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



theorem dyadic_height_dvd_thirty_pow (n : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ n) ∣ 30 ^ n := by
  have h := sorted_height_profile (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at h
  have hd := Nat.mul_dvd_mul
    (Nat.mul_dvd_mul (dvd_refl (2 ^ n)) (pow_dvd_pow 3 h.2))
    (pow_dvd_pow 5 (h.1.trans h.2))
  simpa only [threePrimeHeight, Nat.log_pow (by decide : 1 < (2 : ℕ)),
    ← mul_pow, show (2 : ℕ) * 3 * 5 = 30 from rfl] using hd
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR8
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (q : ℕ) :
    (∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q := by
  constructor
  · intro h
    have hheight : threePrimeHeight 2 3 5 (2 ^ 3) = 120 := by decide +kernel
    have hh : 120 ∣ q ^ 3 := by simpa only [hheight] using h 3 (by decide)
    have h2 : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow
      ((by decide : 2 ∣ 120).trans hh)
    have h3 : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow
      ((by decide : 3 ∣ 120).trans hh)
    have h5 : 5 ∣ q := Nat.prime_five.dvd_of_dvd_pow
      ((by decide : 5 ∣ 120).trans hh)
    have h6 : 6 ∣ q := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    exact (by decide : Nat.Coprime 6 5).mul_dvd_of_dvd_of_dvd h6 h5
  · intro h n _
    exact (dyadic_height_dvd_thirty_pow n).trans (pow_dvd_pow_of_dvd h n)
