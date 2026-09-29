-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.tsum_index_tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:41:47.75043+00:00
-- url     : https://prove2.me/submissions/03ff6aea-25f7-4d45-9824-61c9e656028f

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedSchedule
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
# Pass the uniform finite bound to the actual infinite support

Summability of every series exchanged here precedes the exchange.
No ordinary reciprocal-summability assumption on the support is added.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset Filter
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (g : ℕ → ℝ) (hg : Summable g)
    (hg0 : ∀ a,0≤g a) (n : ℕ) :
    (∑' a, if n≤a then g a else 0) = ∑' k,g (k+n) := by
  classical
  let p : ℕ→ℝ := fun a => if a<n then g a else 0
  let t : ℕ→ℝ := fun a => if n≤a then g a else 0
  have hp : Summable p := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro a; dsimp [p]; split_ifs <;> simp [hg0]
    · intro a; dsimp [p]; split_ifs <;> simp [hg0]
  have ht : Summable t := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro a; dsimp [t]; split_ifs <;> simp [hg0]
    · intro a; dsimp [t]; split_ifs <;> simp [hg0]
  have hpoint : (fun a => p a+t a)=g := by
    funext a
    dsimp [p,t]
    by_cases h : a<n
    · rw [if_pos h,if_neg (by omega),add_zero]
    · rw [if_neg h,if_pos (by omega),zero_add]
  have hsum := hp.tsum_add ht
  rw [hpoint] at hsum
  have hpval : (∑' a,p a)=∑ a∈Finset.range n,g a := by
    rw [tsum_eq_sum (s:=Finset.range n)]
    · apply Finset.sum_congr rfl
      intro a ha
      exact if_pos (Finset.mem_range.mp ha)
    · intro a ha
      exact if_neg (fun h => ha (Finset.mem_range.mpr h))
  rw [hpval] at hsum
  have hsplit := hg.sum_add_tsum_nat_add n
  change (∑' a,t a)=_
  linarith only [hsum,hsplit]
end
