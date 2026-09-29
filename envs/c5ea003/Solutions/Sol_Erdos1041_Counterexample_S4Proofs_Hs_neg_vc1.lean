-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_neg_vc1
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:13:27.419651+00:00
-- url     : https://prove2.me/submissions/8c35c7d8-f15d-4234-84d7-d948c4417c24

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
theorem vc1_p7 : vc1 ^ 7 = (((-424276387488356581112633572628260170755459534206569885263845697514425529 / 250000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-4050884323022818707879129360850140894271366136723211827906450849522615123 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 7 = vc1 ^ 6 * vc1 := by ring
  rw [hs, vc1_p6]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)
theorem qT1_vc1_bound : ‖qT1 vc1‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT2_vc1_bound : ‖qT2 vc1‖ ≤ (33165091 / 6250 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT3_vc1_bound : ‖qT3 vc1‖ ≤ (3638420647 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT4_vc1_bound : ‖qT4 vc1‖ ≤ (29452499 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT5_vc1_bound : ‖qT5 vc1‖ ≤ (218925001 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT6_vc1_bound : ‖qT6 vc1‖ ≤ (22601439 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT0_vc1_re_hi : (qT0 vc1).re ≤ (-24715453 / 50000000000000 : ℝ) := by
  unfold qT0
  rw [vc1_p7, vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem Q_var_vc1 : ∀ w : ℂ, ‖w - vc1‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc1‖ ≤ (33171363740136406876118281397509 / 6250000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc1) (by norm_num)
    qT1_vc1_bound qT2_vc1_bound qT3_vc1_bound qT4_vc1_bound qT5_vc1_bound
    qT6_vc1_bound qT7_bound w hw) (by norm_num)
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ∀ w : ℂ, ‖w - vc1‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc1 qT0_vc1_re_hi (by norm_num)
