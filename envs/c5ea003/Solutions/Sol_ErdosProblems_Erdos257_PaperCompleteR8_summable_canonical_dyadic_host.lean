-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.summable_canonical_dyadic_host
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:59.706711+00:00
-- url     : https://prove2.me/submissions/32f67fdd-d01a-4efa-a057-4314d9c2b6d0

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_frame_literal_weight_sum
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_summable_divisorFrameBudget
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_summable_indicator_frame_union
import Mathlib
import Mathlib.Algebra.BigOperators.Field
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

namespace PaperCompleteR7
end PaperCompleteR7

/-! # Canonical finite-prime weights on the dyadic divisor host

The valuation identity identifies the literal frame budget with the original
finite-prime weighted criterion. A nonnegative finite-subcover argument then
transports summability to the actual infinite union.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset PaperCompleteR7

 theorem primeSetPart_two_dyadic {d : ℕ} (k : ℕ) (hd : ¬ 2 ∣ d) :
    primeSetPart {2} (2 ^ (k + 2) * d) = 2 ^ (k + 2) := by
  have hd0 : d ≠ 0 := by intro h; apply hd; simp [h]
  have hpow0 : 2 ^ (k + 2) ≠ 0 := pow_ne_zero _ (by decide)
  have hfac : (2 ^ (k + 2) * d).factorization 2 = k + 2 := by
    rw [Nat.factorization_mul hpow0 hd0]
    simp [Nat.factorization_pow_self Nat.prime_two, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hd]
  simp [primeSetPart, hfac]

 theorem dyadic_frame_canonical_weight_sum (M k : ℕ) (hodd : ¬ 2 ∣ M) :
    (∑ a ∈ dyadicDivisorFrame M k, primeWeightedTerm 2 {2} a) =
      (∑ d ∈ M.divisors, (1 : ℝ) / d) /
        ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1) := by
  calc
    _ = ∑ a ∈ dyadicDivisorFrame M k,
        ((2 : ℝ) ^ (k + 2)) / ((a : ℝ) * ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1)) := by
      apply sum_congr rfl
      intro a ha
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
      have hdodd : ¬ 2 ∣ d := fun h => hodd (h.trans (Nat.dvd_of_mem_divisors hd))
      simp [primeWeightedTerm, primeSetPart_two_dyadic k hdodd]
    _ = _ := dyadic_frame_literal_weight_sum M k
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
open ErdosProblems.Erdos257.PaperCompleteR7 in
theorem solution (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    Summable (Set.indicator (dyadicDivisorHost (fun k => (P k).prod id))
      (primeWeightedTerm 2 {2})) := by
  have hodd : ∀ k, ¬ 2 ∣ (P k).prod id := by
    intro k h
    obtain ⟨p, hp, hd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff id).mp h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP k p hp).1).mp hd
    have := (hP k p hp).2
    omega
  have hw : ∀ a, 0 ≤ primeWeightedTerm 2 {2} a := by
    intro a
    unfold primeWeightedTerm
    apply div_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    have hpow : (1 : ℝ) ≤ 2 ^ primeSetPart {2} a := one_le_pow₀ (by norm_num)
    exact sub_nonneg.mpr hpow
  apply summable_indicator_frame_union _ _ hw
  have heq : (fun k => ∑ a ∈ dyadicDivisorFrame ((P k).prod id) k,
      primeWeightedTerm 2 {2} a) = (fun k => divisorFrameBudget (P k) k) := by
    funext k
    exact dyadic_frame_canonical_weight_sum _ _ (hodd k)
  rw [heq]
  exact summable_divisorFrameBudget P (fun k p hp => (hP k p hp).1) hS
end
