-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.progressionMean_frame_le_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:28:27.700092+00:00
-- url     : https://prove2.me/submissions/f9021bd4-181c-4375-9614-895cd5289dc6

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_harmonicMass_dyadic_le
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_profileWeight_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_progressionMean_far_conductors_le
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_progressionMean_kernel_le_profile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_reciprocal_le_harmonicMass
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

/-- Linearity for a finite family of actual observables. -/
theorem progressionMean_finsetSum {ι : Type*} (S : Finset ι)
    (u : ι → ℕ → ℝ) (Q T : ℕ) :
    progressionMean Q T (fun N => ∑ i ∈ S, u i N) =
      ∑ i ∈ S, progressionMean Q T (u i) := by
  unfold progressionMean
  rw [Finset.sum_comm, Finset.sum_div]
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution
    (B : ℝ) (hB2 : 2 ≤ B) (Q G j : ℕ) (hQ : 0 < Q) (hG : 0 < G)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (F : Finset ℕ) (hF : ∀ a ∈ F, 0 < a) :
    progressionMean Q (2^j) (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
      (∑ a ∈ F, profileWeight B h a) + profileErrorSum B h F Q j +
      ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/(B^G-1) + 4*(1/2 : ℝ)^j := by
  classical
  let T : ℕ := 2^j
  let S := F.filter (fun a => a ≤ Q*T)
  let U := F.filter (fun a => ¬ a ≤ Q*T)
  let D := B^G-1
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hT : 0 < T := Nat.pow_pos (by decide)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hD : 0 < D := kernel_den_pos hB hG
  have hSa : ∀ a ∈ S, 0 < a := fun a ha => hF a (Finset.mem_filter.mp ha).1
  have hSQT : ∀ a ∈ S, a ≤ Q*T := fun a ha => (Finset.mem_filter.mp ha).2
  have hW : (∑ a ∈ S, profileWeight B h a) ≤ ∑ a ∈ F, profileWeight B h a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a ha _
    exact profileWeight_nonneg B hB h a (hprof a (hF a ha)).1
  have hH : (∑ a ∈ S, 1/(a:ℝ)) ≤ (Q:ℝ)+j :=
    (sum_reciprocal_le_harmonicMass S (Q*T) hSQT).trans (harmonicMass_dyadic_le Q j)
  have hcardNat : S.card ≤ Q*T+1 := by
    calc
      S.card ≤ (Finset.range (Q*T+1)).card :=
        Finset.card_le_card (fun a ha => Finset.mem_range.mpr (by have := hSQT a ha; omega))
      _ = _ := Finset.card_range _
  have hcard : (S.card:ℝ) ≤ ((Q:ℝ)+1)*(T:ℝ) := by
    have hc : (S.card:ℝ) ≤ (Q:ℝ)*(T:ℝ)+1 := by exact_mod_cast hcardNat
    have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
    nlinarith only [hc,hT1]
  have hhigh : (∑ a ∈ S, (G:ℝ)/((a:ℝ)*D)) ≤
      (G:ℝ)*((Q:ℝ)+j)/D := by
    calc
      _ = ((G:ℝ)/D) * ∑ a ∈ S, 1/(a:ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring
      _ ≤ ((G:ℝ)/D) * ((Q:ℝ)+j) :=
        mul_le_mul_of_nonneg_left hH (div_nonneg (Nat.cast_nonneg G) hD.le)
      _ = _ := by ring
  have hcount : (∑ _a ∈ S, 1/((T:ℝ)*D)) ≤ ((Q:ℝ)+1)/D := by
    rw [Finset.sum_const,nsmul_eq_mul]
    have hh := div_le_div_of_nonneg_right hcard (mul_nonneg hTR.le hD.le)
    have hleft : (S.card:ℝ) * (1/((T:ℝ)*D)) = (S.card:ℝ)/((T:ℝ)*D) := by ring
    have hright : (((Q:ℝ)+1)*(T:ℝ))/((T:ℝ)*D) = ((Q:ℝ)+1)/D := by
      field_simp [hTR.ne',hD.ne']
    rw [hleft]
    exact hh.trans_eq hright
  have herr : (∑ a ∈ S, 1/((T:ℝ)*(B^h a-1))) = profileErrorSum B h F Q j := by
    unfold profileErrorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [T]
    simp only [Nat.cast_pow,Nat.cast_ofNat,one_div,mul_inv_rev,inv_pow]
    ring
  have hnear : (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) ≤
      (∑ a ∈ F, profileWeight B h a) + profileErrorSum B h F Q j +
      ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/D := by
    have hb := Finset.sum_le_sum (fun a ha =>
      progressionMean_kernel_le_profile B hB Q G T hQ hG hT h hprof a (hSa a ha))
    simp only [Finset.sum_add_distrib] at hb
    rw [herr] at hb
    change (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) ≤ _ at hb
    have hexpand : ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/D =
        (G:ℝ)*((Q:ℝ)+j)/D + ((Q:ℝ)+1)/D := by ring
    rw [hexpand]
    linarith only [hb,hW,hhigh,hcount]
  have hfar : (∑ a ∈ U, progressionMean Q T (kernelWeight B a)) ≤ 4*(1/2:ℝ)^j := by
    rw [← progressionMean_finsetSum]
    have hh := progressionMean_far_conductors_le B hB2 U Q T hQ hT
      (fun a ha => Nat.lt_of_not_ge (Finset.mem_filter.mp ha).2)
    simpa only [T,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow,div_eq_mul_inv,one_mul] using hh
  have hsplit : (∑ a ∈ F, progressionMean Q T (kernelWeight B a)) =
      (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) +
      ∑ a ∈ U, progressionMean Q T (kernelWeight B a) :=
    (Finset.sum_filter_add_sum_filter_not F (fun a => a ≤ Q*T)
      (fun a => progressionMean Q T (kernelWeight B a))).symm
  rw [progressionMean_finsetSum,hsplit]
  exact add_le_add hnear hfar
end
