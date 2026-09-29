-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.actual_weighted_totient_errorR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:18.635692+00:00
-- url     : https://prove2.me/submissions/55850d5e-5b71-41de-9bfb-7aa0412c03cf

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR14_sourceLogScale_ge_one
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_bounds
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceIntervals_card
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_actual_weighted_blocksR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_harmonic_Icc_boundR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_constant_le_halfR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_totient_constant_posR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_block_prefix_errorR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_sourceJ_tail_boundR16
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





































lemma reciprocal_range_boundR16 (n : ℕ) (hn : 1 ≤ n) (uv : ℚ × ℚ)
    (huv : uv ∈ sourceIntervals) :
    (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      15 * PaperR14.sourceLogScale n := by
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hmin := sourceIntervals_minR16 uv huv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpad : (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      ∑ k ∈ range (n+1), (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ)) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk; exact mem_range.mpr (by have := mem_range.mp hk; omega)
    · intro k hk hnot; positivity
  have hset : range (n+1) = insert 0 (Icc 1 n) := by
    ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hzero : (1 : ℝ)/(uv.1 : ℝ) ≤ 14 := by
    apply (div_le_iff₀ hu).2
    nlinarith
  have hsum : (∑ k ∈ Icc 1 n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      ∑ k ∈ Icc 1 n, (1 : ℝ)/(k : ℝ) := by
    apply sum_le_sum
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)
    exact div_le_div_of_nonneg_left zero_le_one hk0 (by linarith)
  rw [hset, sum_insert (by simp)] at hpad
  simp only [Nat.cast_zero, zero_add] at hpad
  have hh := harmonic_Icc_boundR16 n
  have hl : Real.log n ≤ Real.log ((n : ℝ)+2) := Real.log_le_log hn0 (by linarith)
  have hl0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold PaperR14.sourceLogScale
  nlinarith

lemma source_scaled_log_boundR16 (a n : ℕ) (ha : 1 ≤ a) :
    1 + Real.log (1+(a : ℝ)*(n : ℝ)) ≤ (a : ℝ) * PaperR14.sourceLogScale n := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog := Real.log_le_log (by positivity : 0 < 1+(a : ℝ)*(n : ℝ))
    (show 1+(a : ℝ)*(n : ℝ) ≤ (a : ℝ)*((n : ℝ)+2) by nlinarith)
  rw [Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (n : ℝ)+2 ≠ 0)] at hlog
  have haLog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by linarith)
  have hnLog : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  unfold PaperR14.sourceLogScale
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hnLog]

lemma actual_weighted_finite_errorR16 (n : ℕ) (hn : 1 ≤ n) :
    |(actualWeightedTotientSum n : ℝ) -
      totientConstantR16*(n : ℝ)^2*sourceJPrefixR16 n| ≤
      10920*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  rw [actual_weighted_blocksR16]
  unfold sourceJPrefixR16
  rw [mul_sum, ← sum_sub_distrib]
  have hbound : ∀ uv ∈ sourceIntervals,
      |(∑ k ∈ range n,
        (totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
          totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ))))) -
        totientConstantR16*(n : ℝ)^2*
          (∑ k ∈ range n, blockKernelR16 uv.1 uv.2 k)| ≤
      840*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
    intro uv huv
    rw [mul_sum, ← sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ range n,
          4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
            (1/((k : ℝ)+(uv.1 : ℝ))) :=
        sum_le_sum (fun k hk => block_prefix_errorR16 n k uv huv)
      _ = 4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
          (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) := by rw [mul_sum]
      _ ≤ 4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
          (15*PaperR14.sourceLogScale n) := by
        apply mul_le_mul_of_nonneg_left (reciprocal_range_boundR16 n hn uv huv)
        have hl := Real.log_nonneg
          (show (1 : ℝ) ≤ 1+14*(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])
        exact mul_nonneg (by positivity) (by linarith)
      _ ≤ 840*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
        have hlog := source_scaled_log_boundR16 14 n (by norm_num)
        simp only [Nat.cast_ofNat] at hlog
        have hL := PaperR14.sourceLogScale_ge_one n
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have h := mul_le_mul_of_nonneg_left hlog
          (show 0 ≤ 60*(n : ℝ)*PaperR14.sourceLogScale n by positivity)
        nlinarith
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ uv ∈ sourceIntervals, 840*(n : ℝ)*PaperR14.sourceLogScale n^2 :=
      sum_le_sum hbound
    _ = _ := by simp [sourceIntervals_card]; ring
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
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    |(actualWeightedTotientSum n : ℝ) -
      (totientConstantR16*sourceJR16)*(n : ℝ)^2| ≤
      10927*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  have hfinite := actual_weighted_finite_errorR16 n hn
  obtain ⟨ht0, ht⟩ := sourceJ_tail_boundR16 n
  have hc0 := totient_constant_posR16.le
  have hc := totient_constant_le_halfR16
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := PaperR14.sourceLogScale_ge_one n
  have hLs : 1 ≤ PaperR14.sourceLogScale n^2 := one_le_pow₀ hL
  have hsmall : (n : ℝ)^2 * (13/((n : ℝ)+1/14)^2) ≤ 13 := by
    have hd : (0 : ℝ) < ((n : ℝ)+1/14)^2 := by positivity
    have h : (13*(n : ℝ)^2) / ((n : ℝ)+1/14)^2 ≤ 13 := by
      apply (div_le_iff₀ hd).2
      nlinarith
    convert h using 1 <;> ring
  have htail : |totientConstantR16*(n : ℝ)^2*(sourceJR16-sourceJPrefixR16 n)| ≤
      7*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
    rw [abs_of_nonneg (by positivity)]
    have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ (n : ℝ)^2 by positivity)
    have hc' := mul_le_mul_of_nonneg_left (ht'.trans hsmall) hc0
    have hnL := mul_le_mul_of_nonneg_left hLs (show (0 : ℝ) ≤ n by positivity)
    nlinarith
  have he : (actualWeightedTotientSum n : ℝ) -
      (totientConstantR16*sourceJR16)*(n : ℝ)^2 =
      ((actualWeightedTotientSum n : ℝ) - totientConstantR16*(n : ℝ)^2*sourceJPrefixR16 n) -
        totientConstantR16*(n : ℝ)^2*(sourceJR16-sourceJPrefixR16 n) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith [hfinite, htail])
