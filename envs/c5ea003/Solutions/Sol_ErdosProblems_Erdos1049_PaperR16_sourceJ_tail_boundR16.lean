-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.sourceJ_tail_boundR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:24:33.654363+00:00
-- url     : https://prove2.me/submissions/5383e0ef-6aa7-4207-8c17-7160f93ab2d4

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperShortCapR9
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Definitions.Def_ErdosProblems_Erdos1049_G02WeightedBlocksR16
import Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_bounds
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_card
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

/-! Literal thirteen-block supplier: the complement degree has quadratic rate. -/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000













lemma sourceIntervals_minR16 (uv : ℚ × ℚ) (huv : uv ∈ sourceIntervals) :
    (1/14 : ℝ) ≤ uv.1 := by
  norm_num [sourceIntervals] at huv
  rcases huv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num





lemma trigamma_summableR16 (u : ℝ) (hu : 0 < u) :
    Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + u)^2) := by
  have h := (Real.summable_one_div_nat_add_rpow u (2 : ℝ)).2 (by norm_num)
  simpa only [Real.rpow_two, sq_abs] using h

lemma blockKernel_summableR16 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Summable (blockKernelR16 u v) :=
  (trigamma_summableR16 u hu).sub (trigamma_summableR16 v hv)

lemma blockKernel_nonnegR16 (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (k : ℕ) :
    0 ≤ blockKernelR16 u v k := by
  unfold blockKernelR16
  apply sub_nonneg.mpr
  have hku : 0 < (k : ℝ) + u := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hku)
  nlinarith

lemma trigamma_differenceR16 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∑' k, blockKernelR16 u v k) = trigammaSeriesR16 u - trigammaSeriesR16 v := by
  exact (trigamma_summableR16 u hu).tsum_sub (trigamma_summableR16 v hv)



lemma telescope_rangeR16 (f : ℕ → ℝ) (K N : ℕ) :
    (∑ k ∈ range N, (f (k+K) - f (k+K+1))) = f K - f (N+K) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      convert (show f K - f (N+K) + (f (N+K) - f (N+K+1)) =
        f K - f (N+K+1) by ring) using 1 <;> congr 2 <;> omega

lemma blockKernel_tailR16 (u v : ℝ) (hu : 0 < u) (huv : u < v)
    (hv : v ≤ 1) (K : ℕ) :
    0 ≤ (∑' k : ℕ, blockKernelR16 u v (k+K)) ∧
      (∑' k : ℕ, blockKernelR16 u v (k+K)) ≤ 1 / ((K : ℝ)+u)^2 := by
  have hs := (summable_nat_add_iff K).2
    (blockKernel_summableR16 u v hu (hu.trans huv))
  constructor
  · exact tsum_nonneg (fun k => blockKernel_nonnegR16 u v hu huv.le _)
  · apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
    intro N
    calc
      _ ≤ ∑ k ∈ range N,
          (1 / (((k+K : ℕ) : ℝ)+u)^2 -
            1 / (((k+K+1 : ℕ) : ℝ)+u)^2) := by
        apply sum_le_sum
        intro k hk
        unfold blockKernelR16
        apply sub_le_sub_left
        have hx : (0 : ℝ) ≤ ((k+K : ℕ) : ℝ) := Nat.cast_nonneg _
        have ha : 0 < ((k+K : ℕ) : ℝ) + v := by linarith
        apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        have hle : ((k+K : ℕ) : ℝ) + v ≤ ((k+K+1 : ℕ) : ℝ) + u := by
          push_cast
          linarith
        exact pow_le_pow_left₀ ha.le hle 2
      _ = 1 / ((K : ℝ)+u)^2 - 1 / (((N+K : ℕ) : ℝ)+u)^2 := by
        exact telescope_rangeR16 (fun j => 1 / ((j : ℝ)+u)^2) K N
      _ ≤ _ := sub_le_self _ (by positivity)

lemma sourceJ_tail_identityR16 (N : ℕ) :
    sourceJR16 - sourceJPrefixR16 N =
      ∑ uv ∈ sourceIntervals, ∑' k : ℕ,
        blockKernelR16 (uv.1 : ℝ) (uv.2 : ℝ) (k+N) := by
  unfold sourceJR16 sourceJPrefixR16
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro uv huv
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hs := blockKernel_summableR16 _ _ hu (hu.trans huv')
  have h := hs.sum_add_tsum_nat_add N
  rw [trigamma_differenceR16 _ _ hu (hu.trans huv')] at h
  linarith
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (N : ℕ) :
    0 ≤ sourceJR16 - sourceJPrefixR16 N ∧
      sourceJR16 - sourceJPrefixR16 N ≤ 13 / ((N : ℝ)+1/14)^2 := by
  rw [sourceJ_tail_identityR16]
  constructor
  · apply sum_nonneg
    intro uv huv
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    exact (blockKernel_tailR16 _ _ hu huv' hv N).1
  · calc
      _ ≤ ∑ uv ∈ sourceIntervals, (1 : ℝ)/((N : ℝ)+1/14)^2 := by
        apply sum_le_sum
        intro uv huv
        obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
        apply (blockKernel_tailR16 _ _ hu huv' hv N).2.trans
        have hmin := sourceIntervals_minR16 uv huv
        apply div_le_div_of_nonneg_left (by norm_num)
          (by positivity : (0 : ℝ) < ((N : ℝ)+1/14)^2)
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ = _ := by simp [sourceIntervals_card]; ring
