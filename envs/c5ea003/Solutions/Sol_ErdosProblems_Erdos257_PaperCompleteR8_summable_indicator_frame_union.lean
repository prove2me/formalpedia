-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.summable_indicator_frame_union
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:53:07.081685+00:00
-- url     : https://prove2.me/submissions/8590f53e-49e5-40f3-bdfe-863ec170fe8b

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_finite_frame_subcover
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
theorem solution (G : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : Summable (fun k => ∑ a ∈ G k, w a)) :
    Summable (Set.indicator {a | ∃ k, a ∈ G k} w) := by
  classical
  let A : Set ℕ := {a | ∃ k, a ∈ G k}
  apply summable_of_sum_le (c := ∑' k, ∑ a ∈ G k, w a)
  · intro a
    exact Set.indicator_nonneg (fun a _ => hw a) a
  intro s
  obtain ⟨J, hJ⟩ := exists_finite_frame_subcover (s.filter (· ∈ A)) G
    (fun a ha => (mem_filter.mp ha).2)
  calc
    (∑ a ∈ s, Set.indicator A w a) ≤
        ∑ a ∈ s, ∑ k ∈ J, if a ∈ G k then w a else 0 := by
      apply sum_le_sum
      intro a ha
      by_cases hA : a ∈ A
      · obtain ⟨k, hk, hak⟩ := mem_biUnion.mp (hJ (mem_filter.mpr ⟨ha, hA⟩))
        rw [Set.indicator_of_mem hA]
        have hnonneg : ∀ j ∈ J, 0 ≤ if a ∈ G j then w a else 0 := by
          intro j hj
          by_cases haj : a ∈ G j
          · simp [haj, hw a]
          · simp [haj]
        simpa [hak] using
          (Finset.single_le_sum (f := fun j => if a ∈ G j then w a else 0)
            hnonneg hk)
      · rw [Set.indicator_of_notMem hA]
        exact sum_nonneg (fun k _ => by
          by_cases hak : a ∈ G k
          · simp [hak, hw a]
          · simp [hak])
    _ = ∑ k ∈ J, ∑ a ∈ s, if a ∈ G k then w a else 0 := sum_comm
    _ ≤ ∑ k ∈ J, ∑ a ∈ G k, w a := by
      apply sum_le_sum
      intro k hk
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun a ha => (mem_filter.mp ha).2) (fun a _ _ => hw a)
    _ ≤ ∑' k, ∑ a ∈ G k, w a :=
      hs.sum_le_tsum J (fun k _ => sum_nonneg (fun a _ => hw a))
end
