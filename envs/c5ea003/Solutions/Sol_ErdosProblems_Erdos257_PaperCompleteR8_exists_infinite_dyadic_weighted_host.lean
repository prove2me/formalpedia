-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_infinite_dyadic_weighted_host
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:09:51.144024+00:00
-- url     : https://prove2.me/submissions/9c767c2f-b1c4-42c9-96f9-609ef3b489e8

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicDivisorHost_infinite
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_separating_prime_blocks
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_summable_canonical_dyadic_host
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_zero_not_mem_dyadicDivisorHost
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
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
open ErdosProblems.Erdos257.PaperCompleteR7 in
theorem solution :
    ∃ P : ℕ → Finset ℕ,
      Pairwise (fun k l => Disjoint (P k) (P l)) ∧
      (∀ k, (∀ p ∈ P k, Nat.Prime p ∧ 2 < p) ∧
        (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p ∧
        (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) ∧
      (dyadicDivisorHost (fun k => (P k).prod id)).Infinite ∧
      0 ∉ dyadicDivisorHost (fun k => (P k).prod id) ∧
      FinitePrimeWeighted 2 (dyadicDivisorHost (fun k => (P k).prod id)) := by
  obtain ⟨P, hdis, hP⟩ := exists_separating_prime_blocks
  refine ⟨P, hdis, hP, dyadicDivisorHost_infinite _ ?_,
    zero_not_mem_dyadicDivisorHost _, ?_⟩
  · intro k
    exact prod_pos (fun p hp => ((hP k).1 p hp).1.pos)
  · refine ⟨{2}, by simp, ?_, summable_canonical_dyadic_host P
      (fun k p hp => (hP k).1 p hp) (fun k => (hP k).2.2)⟩
    intro p hp
    have hp2 : p = 2 := mem_singleton.mp hp
    simpa [hp2] using Nat.prime_two
end
