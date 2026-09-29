-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.not_summable_reciprocal_of_unbounded_finite_means
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:09:53.774481+00:00
-- url     : https://prove2.me/submissions/289b648c-e4b3-4c92-854b-75f6c645f76c

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finiteLogarithmicMean_le_reciprocal
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
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (A : Set ℕ) (hA0 : 0 ∉ A)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X) :
    ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) := by
  classical
  intro hs
  obtain ⟨F, hFA, X, hX, hbig⟩ := hlarge
    (Real.exp 1 * ∑' a, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a)
  have hF0 : 0 ∉ F := fun h => hA0 (hFA h)
  have hsum : (∑ a ∈ F, (1 : ℝ) / a) ≤
      ∑' a, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a := by
    have heq : (∑ a ∈ F, (1 : ℝ) / a) =
        ∑ a ∈ F, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Set.indicator_of_mem (hFA ha) (fun a : ℕ => (1 : ℝ) / a)).symm
    rw [heq]
    exact hs.sum_le_tsum F (fun a _ => by
      by_cases ha : a ∈ A
      · rw [Set.indicator_of_mem ha]
        positivity
      · rw [Set.indicator_of_notMem ha])
  have hbound := (finiteLogarithmicMean_le_reciprocal F hF0 X hX).trans
    (mul_le_mul_of_nonneg_left hsum (Real.exp_pos 1).le)
  exact (not_lt_of_ge hbound) hbig
end
