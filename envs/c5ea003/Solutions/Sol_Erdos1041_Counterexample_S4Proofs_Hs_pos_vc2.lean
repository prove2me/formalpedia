-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_pos_vc2
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:18:26.32133+00:00
-- url     : https://prove2.me/submissions/2221d3ac-d816-45d5-a64d-0365e177430a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq0_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq1_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq2_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq3_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq4_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq5_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq6_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qq7_Q
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Hs_pos_on_disk
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_var_vc2
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_vc2_p7
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
theorem qT0_vc2_abs : ‖qT0 vc2‖ ≤ (5980521 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc2_p7, vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem qT0_vc2_re_lo : (35568679 / 10000000000000 : ℝ) ≤ (qT0 vc2).re := by
  unfold qT0
  rw [vc2_p7, vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num
theorem Q_abs_vc2 : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) → ‖Q.eval w‖ ≤ (119610420000095050744432731764040616235381367 / 500000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  have h1 := Q_var_vc2 w hw
  have h2 : ‖Q.eval w‖ ≤ ‖Q.eval w - qT0 vc2‖ + ‖qT0 vc2‖ := by
    calc ‖Q.eval w‖ = ‖(Q.eval w - qT0 vc2) + qT0 vc2‖ := by ring_nf
      _ ≤ ‖Q.eval w - qT0 vc2‖ + ‖qT0 vc2‖ := norm_add_le _ _
  linarith [qT0_vc2_abs]
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) → 0 < Hs w :=
  Hs_pos_on_disk (by norm_num) Q_var_vc2 qT0_vc2_re_lo Q_abs_vc2 (by norm_num)
