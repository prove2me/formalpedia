-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_finite_weighted_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:23:19.81388+00:00
-- url     : https://prove2.me/submissions/2cafd7f7-694a-4151-9ded-e5c52cce726a

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_primeWeightedTerm_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_tsum_index_tail_eq
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
theorem solution (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (E : Set ℕ)
    (hs : Summable (Set.indicator E (primeWeightedTerm b P)))
    {ε : ℝ} (hε : 0<ε) :
    ∃ F : Finset ℕ, (F:Set ℕ) ⊆ E ∧
      Summable (Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P)) ∧
      (∑' a,Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P) a)<ε := by
  classical
  let g := Set.indicator E (primeWeightedTerm b P)
  have hg0 : ∀ a,0≤g a := fun a => Set.indicator_nonneg
    (fun a _ => primeWeightedTerm_nonneg b hb P a) a
  have hlim := tendsto_sum_nat_add g
  have hevent : ∀ᶠ n in atTop,(∑' k,g (k+n))<ε := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := hevent.exists
  let F := (Finset.range n).filter (fun a => a∈E)
  have hFE : (F:Set ℕ) ⊆ E := fun a ha => (Finset.mem_filter.mp ha).2
  have hfun : Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P) =
      fun a => if n≤a then g a else 0 := by
    funext a
    by_cases hEa : a∈E
    · by_cases han : a<n
      · have haF : a∈F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr han,hEa⟩
        simp [haF,han,show ¬n≤a by omega,g]
      · have haF : a∉F := fun ha => han (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        simp [haF,hEa,show n≤a by omega,g]
    · have haF : a∉F := fun ha => hEa (hFE ha)
      simp [hEa,haF,g]
  have htail : Summable (fun a => if n≤a then g a else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro a
      split_ifs
      · exact hg0 a
      · exact le_rfl
    · intro a
      split_ifs
      · exact le_rfl
      · exact hg0 a
  refine ⟨F,hFE,?_,?_⟩
  · rw [hfun]; exact htail
  · rw [hfun,tsum_index_tail_eq g hs hg0 n]
    exact hn
end
