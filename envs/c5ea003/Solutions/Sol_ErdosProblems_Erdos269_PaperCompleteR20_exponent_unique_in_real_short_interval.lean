-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_in_real_short_interval
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:00:43.788253+00:00
-- url     : https://prove2.me/submissions/991fbe48-1668-4972-9623-a1a537f59400

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

namespace ErdosProblems.Erdos269.PaperCompleteR20
open Finset
open scoped BigOperators

noncomputable section

open PaperR10
end
end ErdosProblems.Erdos269.PaperCompleteR20

open Finset
open scoped BigOperators
open PaperR10
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR10 in
theorem solution
    {base a b : ℕ} {lo hi weight : ℝ}
    (hbase : 0 < base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ (base : ℝ) * lo)
    (haLo : lo ≤ (base : ℝ) ^ a * weight)
    (haHi : (base : ℝ) ^ a * weight < hi)
    (hbLo : lo ≤ (base : ℝ) ^ b * weight)
    (hbHi : (base : ℝ) ^ b * weight < hi) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpowNat : base ^ (a + 1) ≤ base ^ b :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpow : (base : ℝ) ^ (a + 1) ≤ (base : ℝ) ^ b := by
      exact_mod_cast hpowNat
    have hbaseR : (0 : ℝ) ≤ base := by positivity
    have hcontra : hi < hi := calc
      hi ≤ (base : ℝ) * lo := hwidth
      _ ≤ (base : ℝ) * ((base : ℝ) ^ a * weight) :=
        mul_le_mul_of_nonneg_left haLo hbaseR
      _ = (base : ℝ) ^ (a + 1) * weight := by rw [pow_succ]; ring
      _ ≤ (base : ℝ) ^ b * weight := mul_le_mul_of_nonneg_right hpow hweight
      _ < hi := hbHi
    exact (lt_irrefl hi hcontra).elim
  · exact hab
  · have hpowNat : base ^ (b + 1) ≤ base ^ a :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpow : (base : ℝ) ^ (b + 1) ≤ (base : ℝ) ^ a := by
      exact_mod_cast hpowNat
    have hbaseR : (0 : ℝ) ≤ base := by positivity
    have hcontra : hi < hi := calc
      hi ≤ (base : ℝ) * lo := hwidth
      _ ≤ (base : ℝ) * ((base : ℝ) ^ b * weight) :=
        mul_le_mul_of_nonneg_left hbLo hbaseR
      _ = (base : ℝ) ^ (b + 1) * weight := by rw [pow_succ]; ring
      _ ≤ (base : ℝ) ^ a * weight := mul_le_mul_of_nonneg_right hpow hweight
      _ < hi := haHi
    exact (lt_irrefl hi hcontra).elim
