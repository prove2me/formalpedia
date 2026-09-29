-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadic_host_unbounded_finite_logarithmic_means
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:13:45.443536+00:00
-- url     : https://prove2.me/submissions/2aa7ebfa-6a4c-4dd6-8e74-5eca9d824cc0

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_finite_logarithmic_growth
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
theorem solution (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    ∀ R : ℝ, ∃ F : Finset ℕ,
      (F : Set ℕ) ⊆ dyadicDivisorHost (fun k => (P k).prod id) ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X := by
  intro R
  let c : ℝ := Real.exp 1 * Real.log 2 / 8
  have hc : 0 < c := div_pos (mul_pos (Real.exp_pos 1) (Real.log_pos (by norm_num)))
    (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (R / c)
  have hRm : R < c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hm
    simpa only [mul_comm] using h
  obtain ⟨X, hX, hbound⟩ := dyadic_finite_logarithmic_growth P m hP hS
  let F := (Finset.range m).biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  refine ⟨F, ?_, X, hX, ?_⟩
  · intro a ha
    obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp ha
    exact ⟨k, hak⟩
  · have heq : c * (m : ℝ) = Real.exp 1 * Real.log 2 * (m : ℝ) / 8 := by
      dsimp [c]
      ring
    rw [heq] at hRm
    exact hRm.trans_le hbound
end
