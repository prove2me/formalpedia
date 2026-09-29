-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_neg_vc5
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:13:40.479694+00:00
-- url     : https://prove2.me/submissions/4ca374ba-ab70-47f2-bfe6-780740801653

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Hs_neg_on_disk
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_var_on_disk
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT7_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq0_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq1_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq2_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq3_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq4_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq5_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq6_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq7_Q
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
theorem vc5_p7 : vc5 ^ 7 = (((-145216936912274390098558476051124713996061929918476991938231577917 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((4143121363288861532431469536381322989930447854768957314173015663188878873 / 625000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 7 = vc5 ^ 6 * vc5 := by ring
  rw [hs, vc5_p6]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)
theorem qT1_vc5_bound : ‖qT1 vc5‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT2_vc5_bound : ‖qT2 vc5‖ ≤ (8406007301 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT3_vc5_bound : ‖qT3 vc5‖ ≤ (2568327519 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT4_vc5_bound : ‖qT4 vc5‖ ≤ (23749329 / 15625 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT5_vc5_bound : ‖qT5 vc5‖ ≤ (259454661 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT6_vc5_bound : ‖qT6 vc5‖ ≤ (615119 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT0_vc5_re_hi : (qT0 vc5).re ≤ (-19464601 / 12500000000000 : ℝ) := by
  unfold qT0
  rw [vc5_p7, vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem Q_var_vc5 : ∀ w : ℂ, ‖w - vc5‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc5‖ ≤ (8407012437656557957315454685604761 / 1000000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc5) (by norm_num)
    qT1_vc5_bound qT2_vc5_bound qT3_vc5_bound qT4_vc5_bound qT5_vc5_bound
    qT6_vc5_bound qT7_bound w hw) (by norm_num)
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ∀ w : ℂ, ‖w - vc5‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc5 qT0_vc5_re_hi (by norm_num)
