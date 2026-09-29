-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean_support_le_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:35:13.754026+00:00
-- url     : https://prove2.me/submissions/b2ec9733-ad76-4206-b1b5-3626dd7ae6cf

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_displacement_eq_tsum
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_summable_displacementAtom
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_profileWeight_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernelWeight_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicMean_finite_frame_le_profile
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicMean_finsetSum
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadicMean_mono
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_summable_progressionMean
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_tsum_dyadicMean
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

/-- Summability through the two FINITE averaging operations. -/
theorem summable_dyadicMean {ι : Type*} (u : ι → ℕ → ℝ)
    (hu : ∀ N, Summable (fun i => u i N)) (Q R M : ℕ) :
    Summable (fun i => dyadicMean Q R M (u i)) := by
  have hs : Summable (fun i => ∑ j ∈ Finset.Ico R (R+M),
      progressionMean Q (2^j) (u i)) :=
    summable_sum (fun j _ => summable_progressionMean u hu Q (2^j))
  exact hs.div_const (M:ℝ)

theorem kernelWeight_nat_eq_shiftedRadixAtom (b N d : ℕ) :
    kernelWeight (b:ℝ) d N = Erdos249257.shiftedRadixAtom b N d := by
  by_cases hd : d=0
  · subst d; simp [kernelWeight,Erdos249257.shiftedRadixAtom]
  · simp only [kernelWeight,Erdos249257.shiftedRadixAtom,hd,if_false]

/-- A finite support displacement is bounded by its actual real-base potential. -/
theorem finite_displacement_le_kernelSum (b : ℕ) (hb : 2 ≤ b)
    (F : Finset ℕ) (N : ℕ) :
    displacement b (F:Set ℕ) N ≤ ∑ a ∈ F, kernelWeight (b:ℝ) a N := by
  classical
  rw [displacement_eq_tsum b (F:Set ℕ) N hb]
  rw [tsum_eq_sum (s:=F)]
  · apply Finset.sum_le_sum
    intro a ha
    rw [Set.indicator_of_mem (show a∈(F:Set ℕ) from ha),displacementAtom,
      ← kernelWeight_nat_eq_shiftedRadixAtom,← kernelWeight_nat_eq_shiftedRadixAtom]
    exact sub_le_self _ (kernelWeight_nonneg (by exact_mod_cast (by omega : 1<b)) a 0)
  · intro a ha
    simp [ha]
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset Filter
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution
    (b : ℕ) (hb : 2 ≤ b) (E : Set ℕ) (hE0 : 0 ∉ E)
    (Q G M : ℕ) (hQ : 0 < Q) (hG : 0 < G) (hM : 0 < M)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (hs : Summable (Set.indicator E (profileWeight (b:ℝ) h))) :
    dyadicMean Q M M (displacement b E) ≤
      (1+2*(Q:ℝ)/M) * (∑' a, Set.indicator E (profileWeight (b:ℝ) h) a) +
      weightedScheduleError (b:ℝ) Q G M := by
  classical
  let u : ℕ → ℕ → ℝ := fun a N => Set.indicator E (displacementAtom b N) a
  let w := Set.indicator E (profileWeight (b:ℝ) h)
  let K : ℝ := 1+2*(Q:ℝ)/M
  let e := weightedScheduleError (b:ℝ) Q G M
  have hu : ∀ N, Summable (fun a => u a N) := fun N =>
    summable_displacementAtom b E N hb
  have hmeans := summable_dyadicMean u hu Q M M
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (1:ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hw0 : ∀ a, 0 ≤ w a := by
    intro a
    by_cases ha : a∈E
    · have hap : 0<a := Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ ha))
      simpa [w,ha] using profileWeight_nonneg (b:ℝ) hb1 h a (hprof a hap).1
    · simp [w,ha]
  have hfinite : ∀ S : Finset ℕ,
      (∑ a ∈ S, dyadicMean Q M M (u a)) ≤ K*(∑' a,w a)+e := by
    intro S
    let F := S.filter (fun a => a∈E)
    have hFpos : ∀ a∈F,0<a := by
      intro a ha
      have hEa := (Finset.mem_filter.mp ha).2
      exact Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ hEa))
    have hval : ∀ N, (∑ a ∈ S,u a N)=displacement b (F:Set ℕ) N := by
      intro N
      rw [displacement_eq_tsum b (F:Set ℕ) N hb]
      rw [tsum_eq_sum (s:=F)]
      · have hh : (∑ a ∈ F,Set.indicator (F:Set ℕ) (displacementAtom b N) a) =
            ∑ a ∈ F,displacementAtom b N a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Set.indicator_of_mem (show a∈(F:Set ℕ) from ha) _
        rw [hh]
        dsimp [F,u]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hEa : a∈E <;> simp [hEa]
      · intro a ha
        simp [ha]
    have hmeanEq : (∑ a ∈ S,dyadicMean Q M M (u a)) =
        dyadicMean Q M M (displacement b (F:Set ℕ)) := by
      rw [← dyadicMean_finsetSum]
      exact congrArg (dyadicMean Q M M) (funext hval)
    have hfiniteBound := dyadicMean_finite_frame_le_profile (b:ℝ) hbR Q G M hQ hG hM h hprof F hFpos
    have hdisp := dyadicMean_mono Q M M (displacement b (F:Set ℕ))
      (fun N => ∑ a∈F,kernelWeight (b:ℝ) a N)
      (finite_displacement_le_kernelSum b hb F)
    have hWF : (∑ a∈F,profileWeight (b:ℝ) h a) ≤ ∑' a,w a := by
      have heq : (∑ a∈F,profileWeight (b:ℝ) h a) = ∑ a∈F,w a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (Set.indicator_of_mem (Finset.mem_filter.mp ha).2 _).symm
      rw [heq]
      exact hs.sum_le_tsum F (fun a _ => hw0 a)
    have hscale := mul_le_mul_of_nonneg_left hWF (by positivity : 0≤K)
    rw [hmeanEq]
    -- Expose the error package: the finite theorem associates its two errors differently.
    dsimp [K, e, weightedScheduleError] at hscale ⊢
    linarith only [hdisp, hfiniteBound, hscale]
  have ht := hmeans.tsum_le_of_sum_le hfinite
  rw [tsum_dyadicMean u hu Q M M] at ht
  have hfun : (fun N => ∑' a,u a N)=displacement b E := by
    funext N
    exact (displacement_eq_tsum b E N hb).symm
  rw [hfun] at ht
  exact ht
end
