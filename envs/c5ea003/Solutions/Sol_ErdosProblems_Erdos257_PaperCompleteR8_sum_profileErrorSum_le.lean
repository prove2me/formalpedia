-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.sum_profileErrorSum_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:08:56.51687+00:00
-- url     : https://prove2.me/submissions/76509fec-cd9e-4981-80f6-de24b36519d2

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteMean
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_dyadic_observation_sum_le
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

/-! Finite weighted mean assembly. No mean limit is assumed. -/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB : 1 < B)
    (h : ℕ → ℕ) (F J : Finset ℕ) (Q : ℕ)
    (hF : ∀ a ∈ F, 0 < a) (hh : ∀ a ∈ F, 0 < h a) :
    (∑ j ∈ J, profileErrorSum B h F Q j) ≤
      2*(Q:ℝ) * ∑ a ∈ F, profileWeight B h a := by
  have hnn : ∀ a ∈ F, 0 ≤ 1/(B^h a-1) :=
    fun a ha => one_div_nonneg.mpr (kernel_den_pos hB (hh a ha)).le
  have hobs := dyadic_observation_sum_le J F Q (fun a => 1/(B^h a-1)) hF hnn
  have hw : (∑ a ∈ F, (1/(B^h a-1))/(a:ℝ)) ≤
      ∑ a ∈ F, profileWeight B h a := by
    apply Finset.sum_le_sum
    intro a ha
    have hh1 : (1:ℝ) ≤ h a := by exact_mod_cast (hh a ha)
    have hd : 0 ≤ (a:ℝ)*(B^h a-1) :=
      mul_nonneg (Nat.cast_nonneg a) (kernel_den_pos hB (hh a ha)).le
    have hp := div_le_div_of_nonneg_right hh1 hd
    calc
      (1/(B^h a-1))/(a:ℝ) = 1/((a:ℝ)*(B^h a-1)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (h a:ℝ)/((a:ℝ)*(B^h a-1)) := hp
      _ = profileWeight B h a := rfl
  exact hobs.trans (mul_le_mul_of_nonneg_left hw (by positivity))
end
