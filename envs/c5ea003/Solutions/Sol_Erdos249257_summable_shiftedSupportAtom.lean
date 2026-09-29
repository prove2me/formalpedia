-- Prove2me | solution 1 for Erdos249257.summable_shiftedSupportAtom
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:13:45.107153+00:00
-- url     : https://prove2.me/submissions/d1e10d3e-ab6d-45c7-89ab-881ce66cc719

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Definitions.Def_Erdos249257_GenericTailOrbitRigidity
import Definitions.Def_Erdos249257_GreedyAchievementSet
import Definitions.Def_Erdos249257_RationalSupportCarrySkeleton
import Definitions.Def_Erdos249257_ReciprocalSupportIrrationality
import Theorems.Thm_Erdos249257_summable_erdosSupport_indicator
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Perfect

namespace TotientTailPeriodKiller
end TotientTailPeriodKiller

/-!
# Reciprocal-summable support irrationality

This module develops the shifted-atom description of binary support tails.
-/

namespace Erdos249257
open Filter Set
open TotientTailPeriodKiller

noncomputable section





theorem shiftedMersenneAtom_nonneg (N d : ℕ) :
    0 ≤ shiftedMersenneAtom N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom, if_neg hd.ne']
    have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    positivity



/-! ## GCD orbit means -/













































theorem shiftedMersenneAtom_le_pow_mul_zero (N d : ℕ) :
    shiftedMersenneAtom N d ≤
      (2 : ℝ) ^ N * ((1 : ℝ) / ((2 : ℝ) ^ d - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom, if_neg hd.ne']
    have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    have hmod : N % d ≤ N := Nat.mod_le _ _
    have hp : (2 : ℝ) ^ (N % d) ≤ (2 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) hmod
    calc
      (2 : ℝ) ^ (N % d) / ((2 : ℝ) ^ d - 1) =
          (2 : ℝ) ^ (N % d) * (1 / ((2 : ℝ) ^ d - 1)) := by ring
      _ ≤ (2 : ℝ) ^ N * (1 / ((2 : ℝ) ^ d - 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
end
end Erdos249257

open Filter Set
open TotientTailPeriodKiller
open Erdos249257 in
open Erdos249257.TotientTailPeriodKiller in
theorem solution (A : Set ℕ) (N : ℕ) :
    Summable (shiftedSupportAtom A N) := by
  have hbase := summable_erdosSupport_indicator 2 A (by norm_num)
  have hscaled : Summable (fun d : ℕ =>
      (2 : ℝ) ^ N *
        Set.indicator A (fun d => (1 : ℝ) / ((2 : ℝ) ^ d - 1)) d) :=
    hbase.mul_left ((2 : ℝ) ^ N)
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hscaled
  · exact Set.indicator_nonneg
      (fun d _ => shiftedMersenneAtom_nonneg N d) d
  · by_cases hdA : d ∈ A
    · simp only [shiftedSupportAtom, Set.indicator_of_mem hdA]
      exact shiftedMersenneAtom_le_pow_mul_zero N d
    · simp [shiftedSupportAtom, hdA]
