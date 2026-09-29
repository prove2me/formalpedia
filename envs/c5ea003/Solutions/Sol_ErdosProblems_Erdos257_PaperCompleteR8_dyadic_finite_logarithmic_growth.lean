-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadic_finite_logarithmic_growth
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:09:52.444306+00:00
-- url     : https://prove2.me/submissions/a5be82ac-28a8-40d6-b9ac-9cc5a10ec17f

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicBlockCount_cast
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_union_log_pointwise
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_dyadic_event_period
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_mean_prime_block_dyadic_events
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



/-- Exact mean of all block counts, before imposing the harmonic scale. -/
theorem mean_dyadicBlockCounts (P : ℕ → Finset ℕ) (J : Finset ℕ) (X : ℕ)
    (hP : ∀ k p, p ∈ P k → 0 < p) (hX : 0 < X)
    (hperiod : ∀ k ∈ J, ∀ p ∈ P k, 2 * (2 ^ (k + 2) * p) ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) / X =
      ∑ k ∈ J, (∑ p ∈ P k, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
  classical
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [dyadicBlockCount_cast]
  exact mean_prime_block_dyadic_events (P k) (k + 2) X (hP k) hX (hperiod k hk)

/-- Each prescribed row contributes at least one eighth to the event mean. -/
theorem harmonic_row_event_lower (P : Finset ℕ) (k : ℕ)
    (hS : (2 : ℝ) ^ k ≤ ∑ p ∈ P, (1 : ℝ) / p) :
    (1 / 8 : ℝ) ≤ (∑ p ∈ P, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ (k + 2))).2
  rw [pow_add]
  convert hS using 1 <;> ring
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (P : ℕ → Finset ℕ) (m : ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    ∃ X : ℕ, 0 < X ∧
      Real.exp 1 * Real.log 2 * (m : ℝ) / 8 ≤
        finiteLogarithmicMean
          ((Finset.range m).biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)) X := by
  classical
  let J := Finset.range m
  let F := J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  obtain ⟨X, hX, hperiod⟩ := exists_dyadic_event_period P J
    (fun k p hp => (hP k p hp).1.pos)
  refine ⟨X, hX, ?_⟩
  have havg := mean_dyadicBlockCounts P J X
    (fun k p hp => (hP k p hp).1.pos) hX hperiod
  have hrows : (m : ℝ) / 8 ≤
      ∑ k ∈ J, (∑ p ∈ P k, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
    have h := Finset.sum_le_sum (s := J) (fun k _ => harmonic_row_event_lower (P k) k (hS k))
    simpa only [Finset.sum_const, nsmul_eq_mul, J, Finset.card_range, div_eq_mul_inv, one_mul] using h
  have hc : 0 ≤ Real.exp 1 * Real.log 2 := mul_nonneg (Real.exp_pos 1).le
    (Real.log_nonneg (by norm_num))
  have hpoint : ∀ n ∈ Icc 1 X,
      Real.exp 1 * Real.log 2 * (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) ≤
        Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) := by
    intro n hn
    have hp := dyadic_union_log_pointwise P J n (by
      have := (Finset.mem_Icc.mp hn).1
      omega) hP
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le
  have hmean : Real.exp 1 * Real.log 2 *
      ((∑ n ∈ Icc 1 X, ∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) / X) ≤
        finiteLogarithmicMean F X := by
    rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (Nat.cast_nonneg X)
  rw [havg] at hmean
  have hscaled := mul_le_mul_of_nonneg_left hrows hc
  have htotal := hscaled.trans hmean
  simpa only [mul_div_assoc] using htotal
end
