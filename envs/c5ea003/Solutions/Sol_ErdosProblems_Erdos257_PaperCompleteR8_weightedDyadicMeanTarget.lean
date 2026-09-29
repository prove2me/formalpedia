-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.weightedDyadicMeanTarget
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:37:24.479067+00:00
-- url     : https://prove2.me/submissions/2cb6baa1-58e4-4901-8666-0af6ac60346a

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_MixedGaugeConsumer
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteEstimates
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedSchedule
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicMean_remove_annihilated_prefix
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicMean_support_le_profile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeWeightedTerm_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_finite_weighted_tail
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_large_half_pow_lt
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_left_dvd_primeSamplingModulus
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeProduct_ge_two
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSamplingModulus_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeSamplingModulus_profile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_weightedScheduleError_le
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
# End-to-end weighted and mixed support candidates

This module proves the previously isolated weighted finite-mean
producer from the actual FinitePrimeWeighted data. It does not assume that
producer. The concluding declarations assert precisely the two Prop-valued
paper goals; the separate strengthened positive-cover goal is proved in
PositiveCoverReturn. No parent statement is asserted.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution : WeightedDyadicMeanTarget := by
  classical
  intro b E hb hE0 hE ε hε L₀ hL₀
  obtain ⟨P,hPn,hP,hs⟩ := hE
  obtain ⟨F,hFE,hTail,hSmall⟩ := exists_finite_weighted_tail b hb P E hs
    (div_pos hε (by norm_num : (0:ℝ)<4))
  have hFpos : ∀ a∈F,0<a := by
    intro a ha
    exact Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ hFE ha))
  let L := L₀ * F.prod id
  have hL : 0<L := Nat.mul_pos hL₀ (Finset.prod_pos hFpos)
  have hL₀L : L₀∣L := dvd_mul_right _ _
  have hFL : ∀ a∈F,a∣L := fun a ha =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id ha) L₀
  let c := P.prod id
  have hc : 2≤c := primeProduct_ge_two P hPn hP
  obtain ⟨H,hH,Hsmall⟩ := exists_large_half_pow_lt (max 4 (L+c+2))
    (div_pos hε (by norm_num : (0:ℝ)<64))
  have hH4 : 4≤H := (le_max_left _ _).trans hH
  have hHC : L+c+2≤H := (le_max_right _ _).trans hH
  let Q := primeSamplingModulus L P H
  let G : ℕ := 2^H
  let M := 4*Q
  let D := E \ (F:Set ℕ)
  have hQ : 0<Q := primeSamplingModulus_pos hL P hP H
  have hG : 0<G := Nat.pow_pos (by decide)
  have hM : 0<M := Nat.mul_pos (by decide) hQ
  have hLQ : L∣Q := left_dvd_primeSamplingModulus L P H
  have hFQ : ∀ a∈F,a∣Q := fun a ha => (hFL a ha).trans hLQ
  have hD0 : 0∉D := fun hd => hE0 hd.1
  have hprof : GcdProfile Q G (primeSetPart P) := primeSamplingModulus_profile hL P hP H
  let W := ∑' a,Set.indicator D (primeWeightedTerm b P) a
  have hW0 : 0≤W := tsum_nonneg (fun a => Set.indicator_nonneg
    (fun a _ => primeWeightedTerm_nonneg b hb P a) a)
  have hWsmall : W<ε/4 := hSmall
  have hMean := dyadicMean_support_le_profile b hb D hD0 Q G M hQ hG hM
    (primeSetPart P) hprof hTail
  have hEbound : weightedScheduleError (b:ℝ) Q G M ≤ 26*(1/2:ℝ)^H :=
    weightedScheduleError_le (b:ℝ) (by exact_mod_cast hb) L c H hL hc hH4 hHC
  have hQreal : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have hfactor : 1+2*(Q:ℝ)/(M:ℝ)≤2 := by
    dsimp [M]
    push_cast
    have heq : 1+2*(Q:ℝ)/(4*(Q:ℝ))=(3/2:ℝ) := by
      field_simp [hQreal]
      <;> ring
    rw [heq]
    norm_num
  have hscale := mul_le_mul_of_nonneg_right hfactor hW0
  have hsmall : dyadicMean Q M M (displacement b D)<ε := by
    change dyadicMean Q M M (displacement b D) ≤
      (1+2*(Q:ℝ)/M)*W + weightedScheduleError (b:ℝ) Q G M at hMean
    nlinarith only [hMean,hscale,hEbound,hWsmall,Hsmall,hε]
  refine ⟨Q,M,M,hQ,hL₀L.trans hLQ,le_rfl,?_⟩
  rw [dyadicMean_remove_annihilated_prefix b hb E F hFE Q M M hFQ]
  exact hsmall
end
