-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean_finite_frame_le_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:26.21041+00:00
-- url     : https://prove2.me/submissions/e7eb4118-8d11-496f-aeac-15a6432c77f1

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_progressionMean_frame_le_profile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_profileErrorSum_le
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
theorem solution
    (B : ℝ) (hB2 : 2 ≤ B) (Q G M : ℕ)
    (hQ : 0 < Q) (hG : 0 < G) (hM : 0 < M)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (F : Finset ℕ) (hF : ∀ a ∈ F, 0 < a) :
    dyadicMean Q M M (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
      (1+2*(Q:ℝ)/M) * (∑ a ∈ F, profileWeight B h a) +
      ((G:ℝ)*((Q:ℝ)+2*(M:ℝ))+(Q:ℝ)+1)/(B^G-1) + 4*(1/2:ℝ)^M := by
  let J := Finset.Ico M (M+M)
  let W := ∑ a ∈ F, profileWeight B h a
  let E := ((G:ℝ)*((Q:ℝ)+2*(M:ℝ))+(Q:ℝ)+1)/(B^G-1)
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hD : 0 < B^G-1 := kernel_den_pos hB hG
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hcard : J.card=M := by dsimp [J]; rw [Nat.card_Ico]; omega
  have hrow : ∀ j ∈ J,
      progressionMean Q (2^j) (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
        W + profileErrorSum B h F Q j + E + 4*(1/2:ℝ)^M := by
    intro j hj
    have hlow : M ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : (j:ℝ) ≤ 2*(M:ℝ) := by
      exact_mod_cast (Nat.le_of_lt (by have := (Finset.mem_Ico.mp hj).2; omega : j < 2*M))
    have hbound := progressionMean_frame_le_profile B hB2 Q G j hQ hG h hprof F hF
    have hh : ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/(B^G-1) ≤ E := by
      apply div_le_div_of_nonneg_right _ hD.le
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hj2 (Q:ℝ)) (Nat.cast_nonneg G)
      linarith only [hm]
    have hgeo : (1/2:ℝ)^j ≤ (1/2:ℝ)^M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlow
    dsimp [W]
    linarith only [hbound,hh,hgeo]
  have hobs := sum_profileErrorSum_le B hB h F J Q hF
    (fun a ha => (hprof a (hF a ha)).1)
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcard] at hsum
  have hsum' : (∑ j ∈ J, progressionMean Q (2^j)
      (fun N => ∑ a ∈ F, kernelWeight B a N)) ≤
      (M:ℝ)*W + 2*(Q:ℝ)*W + (M:ℝ)*E + (M:ℝ)*(4*(1/2:ℝ)^M) := by
    linarith only [hsum,hobs]
  have hdiv := div_le_div_of_nonneg_right hsum' hMR.le
  have heq : ((M:ℝ)*W + 2*(Q:ℝ)*W + (M:ℝ)*E + (M:ℝ)*(4*(1/2:ℝ)^M))/(M:ℝ) =
      (1+2*(Q:ℝ)/M)*W + E + 4*(1/2:ℝ)^M := by
    field_simp [hMR.ne']
    <;> ring
  exact hdiv.trans_eq heq
end
