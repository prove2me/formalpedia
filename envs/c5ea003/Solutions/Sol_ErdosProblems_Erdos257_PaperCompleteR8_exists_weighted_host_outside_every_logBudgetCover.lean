-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_host_outside_every_logBudgetCover
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:17:10.268689+00:00
-- url     : https://prove2.me/submissions/c391bf01-1db2-459b-b75a-0766c6c2436f

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
import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_MixedGaugeConsumer
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteEstimates
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedSchedule
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisibilityWeightedClaim
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_host_unbounded_finite_logarithmic_means
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_infinite_dyadic_weighted_host
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_no_logBudgetCover_of_unbounded_finite_means
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_not_summable_reciprocal_of_unbounded_finite_means
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
import Mathlib.NumberTheory.SumPrimeReciprocals
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

   
                                                                         

                                                                 
                                                                      
                                                                        
                                                                             
  
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7















/-- No strengthened positive cover, with arbitrary positive weights, covers this host. -/
theorem no_logBudgetCover_dyadic_host (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    IsEmpty (LogBudgetCover (dyadicDivisorHost (fun k => (P k).prod id))) :=
  no_logBudgetCover_of_unbounded_finite_means _
    (dyadic_host_unbounded_finite_logarithmic_means P hP hS)
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (Erdos249257.erdosSupportSeries b B)) := by
  obtain ⟨P, hdis, hP, hinf, hzero, hweighted⟩ := exists_infinite_dyadic_weighted_host
  let A := dyadicDivisorHost (fun k => (P k).prod id)
  have hpr : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p := fun k p hp => (hP k).1 p hp
  have hscale : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p := fun k => (hP k).2.1
  have hlarge := dyadic_host_unbounded_finite_logarithmic_means P hpr hscale
  refine ⟨A, hinf, hzero, hweighted,
    not_summable_reciprocal_of_unbounded_finite_means A hzero hlarge,
    no_logBudgetCover_dyadic_host P hpr hscale, ?_⟩
  exact divisibilityWeightedClaim.2 A hzero hweighted
end
