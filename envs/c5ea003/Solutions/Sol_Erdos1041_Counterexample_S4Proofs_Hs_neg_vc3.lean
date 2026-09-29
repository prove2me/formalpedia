-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_neg_vc3
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:13:28.153878+00:00
-- url     : https://prove2.me/submissions/2c8d1eef-8e6b-4634-bbec-a651f79b6c02

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
theorem vc3_p7 : vc3 ^ 7 = (((-542720218487546308151652214037299123264253021909490678306845691 / 9765625000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-616385022012704705237035105169518627393915772679675375255529670880137 / 9765625000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 7 = vc3 ^ 6 * vc3 := by ring
  rw [hs, vc3_p6]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)
theorem qT1_vc3_bound : ‖qT1 vc3‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT2_vc3_bound : ‖qT2 vc3‖ ≤ (10805001 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT3_vc3_bound : ‖qT3 vc3‖ ≤ (167933059 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT4_vc3_bound : ‖qT4 vc3‖ ≤ (25850669 / 125000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT5_vc3_bound : ‖qT5 vc3‖ ≤ (17158861 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT6_vc3_bound : ‖qT6 vc3‖ ≤ (6327507 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT0_vc3_re_hi : (qT0 vc3).re ≤ (-186589 / 2500000000000 : ℝ) := by
  unfold qT0
  rw [vc3_p7, vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem Q_var_vc3 : ∀ w : ℂ, ‖w - vc3‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc3‖ ≤ (4522033986653161084127091331003 / 200000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc3) (by norm_num)
    qT1_vc3_bound qT2_vc3_bound qT3_vc3_bound qT4_vc3_bound qT5_vc3_bound
    qT6_vc3_bound qT7_bound w hw) (by norm_num)
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ∀ w : ℂ, ‖w - vc3‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc3 qT0_vc3_re_hi (by norm_num)
