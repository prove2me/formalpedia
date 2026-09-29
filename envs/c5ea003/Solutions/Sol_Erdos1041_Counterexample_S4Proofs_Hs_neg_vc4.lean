-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_neg_vc4
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:13:39.998737+00:00
-- url     : https://prove2.me/submissions/ca15d9c1-c39e-4ec6-87c6-112852aaadc4

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
theorem vc4_p7 : vc4 ^ 7 = (((1133905328439280208585693561539832422428460918077690658482459 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-1347283458285099461755927652123069767085316471437075724564630218163 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 7 = vc4 ^ 6 * vc4 := by ring
  rw [hs, vc4_p6]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)
theorem qT1_vc4_bound : ‖qT1 vc4‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT2_vc4_bound : ‖qT2 vc4‖ ≤ (754797 / 31250 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT3_vc4_bound : ‖qT3 vc4‖ ≤ (117439299 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT4_vc4_bound : ‖qT4 vc4‖ ≤ (116999319 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT5_vc4_bound : ‖qT5 vc4‖ ≤ (74527431 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT6_vc4_bound : ‖qT6 vc4‖ ≤ (2637403 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT0_vc4_re_hi : (qT0 vc4).re ≤ (-86373977 / 100000000000000 : ℝ) := by
  unfold qT0
  rw [vc4_p7, vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem Q_var_vc4 : ∀ w : ℂ, ‖w - vc4‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc4‖ ≤ (3144217359853999839065930523377 / 125000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc4) (by norm_num)
    qT1_vc4_bound qT2_vc4_bound qT3_vc4_bound qT4_vc4_bound qT5_vc4_bound
    qT6_vc4_bound qT7_bound w hw) (by norm_num)
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ∀ w : ℂ, ‖w - vc4‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc4 qT0_vc4_re_hi (by norm_num)
