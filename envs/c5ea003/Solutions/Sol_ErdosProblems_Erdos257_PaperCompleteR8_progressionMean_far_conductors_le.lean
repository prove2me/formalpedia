-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.progressionMean_far_conductors_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:23:21.210351+00:00
-- url     : https://prove2.me/submissions/bfb0ce1d-b803-4fe1-9bac-f70c73910493

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
import Definitions.Def_Erdos249257_AllBaseReciprocalSupportIrrationality
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteEstimates
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernelWeight_nowrap_binary_envelope
import Theorems.Thm_ErdosProblems_Erdos257_sum_half_pow_le_twice_min
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Tactic
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

/-!
# Finite weighted estimates with an explicit observation window

The high-GCD remainder is charged against a dyadic harmonic
bound, not against the cardinality of an unbounded conductor support.
The future-conductor contribution is bounded geometrically before any
infinite interchange. All constants here are deliberately non-sharp.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7



/-- The last term controls a finite geometric progression whose ratio is >=2. -/
theorem positive_geometric_sum_le_twice_last (C : ℝ) (hC : 2 ≤ C) (T : ℕ) :
    (∑ m ∈ Finset.range T, C ^ (m + 1)) ≤ 2 * C ^ T := by
  have hC1 : 1 < C := lt_of_lt_of_le (by norm_num) hC
  have hgap : 0 < C - 1 := sub_pos.mpr hC1
  have hCT : 0 ≤ C ^ T := pow_nonneg (le_trans (by norm_num) hC) _
  have hsum : (∑ m ∈ Finset.range T, C ^ (m + 1)) = C * ((C ^ T - 1)/(C - 1)) := by
    simp_rw [pow_succ']
    rw [← Finset.mul_sum, geom_sum_eq hC1.ne']
  rw [hsum, ← mul_div_assoc]
  apply (div_le_iff₀ hgap).mpr
  have hn := mul_nonneg hCT (sub_nonneg.mpr hC)
  nlinarith only [hn, hC]
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB2 : 2 ≤ B)
    (F : Finset ℕ) (Q T : ℕ) (hQ : 0 < Q) (hT : 0 < T)
    (hfar : ∀ a ∈ F, Q * T < a) :
    progressionMean Q T (fun N => ∑ a ∈ F, kernelWeight B a N) ≤ 4 / (T : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hgeo := sum_half_pow_le_twice_min F (Q * T + 1)
    (fun a ha => Nat.succ_le_of_lt (hfar a ha))
  have hrow : ∀ m ∈ Finset.range T,
      (∑ a ∈ F, kernelWeight B a ((m + 1)*Q)) ≤
        2 * (2 : ℝ) ^ ((m + 1)*Q) / 2 ^ (Q*T) := by
    intro m hm
    have hmq : (m + 1)*Q ≤ Q*T := by
      have hh := Nat.mul_le_mul_right Q (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
      simpa only [Nat.mul_comm] using hh
    calc
      _ ≤ ∑ a ∈ F, 2 * (2 : ℝ) ^ ((m + 1)*Q) * (1/2 : ℝ) ^ a :=
        Finset.sum_le_sum (fun a ha => kernelWeight_nowrap_binary_envelope B hB2 a _
          (lt_of_le_of_lt hmq (hfar a ha)))
      _ = 2 * (2 : ℝ) ^ ((m + 1)*Q) * ∑ a ∈ F, (1/2 : ℝ) ^ a := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (2 : ℝ) ^ ((m + 1)*Q) * (2 * (1/2 : ℝ) ^ (Q*T+1)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = _ := by
        rw [pow_succ, one_div, inv_pow]
        ring
  have hC : (2 : ℝ) ≤ (2 : ℝ) ^ Q := le_self_pow₀ (by norm_num) hQ.ne'
  have hpowSum : (∑ m ∈ Finset.range T, (2 : ℝ) ^ ((m + 1)*Q)) ≤
      2 * (2 : ℝ) ^ (Q*T) := by
    have hh := positive_geometric_sum_le_twice_last ((2 : ℝ)^Q) hC T
    simpa only [← pow_mul, Nat.mul_comm] using hh
  have hsum : (∑ m ∈ Finset.range T, ∑ a ∈ F, kernelWeight B a ((m + 1)*Q)) ≤ 4 := by
    calc
      _ ≤ ∑ m ∈ Finset.range T, 2 * (2 : ℝ) ^ ((m + 1)*Q) / 2 ^ (Q*T) :=
        Finset.sum_le_sum hrow
      _ = 2 * (∑ m ∈ Finset.range T, (2 : ℝ) ^ ((m + 1)*Q)) / 2 ^ (Q*T) := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ 2 * (2 * (2 : ℝ) ^ (Q*T)) / 2 ^ (Q*T) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowSum (by norm_num)) (by positivity)
      _ = 4 := by field_simp <;> norm_num
  exact div_le_div_of_nonneg_right hsum hT0.le
end
