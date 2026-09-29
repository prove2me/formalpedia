-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.zs_simple
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:29:28.723189+00:00
-- url     : https://prove2.me/submissions/6a46fcec-2fc6-4778-8710-da7a09d00d7f

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_derivative_f_eval_rho_eps
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_derivative_f_natDegree
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_zs_crit
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rootMultiplicity_eq_one_of_nodup
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
noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
theorem lt_norm_of_lt_normSq {z : ℂ} {m : ℝ} (hm : 0 ≤ m)
    (h : m ^ 2 < Complex.normSq z) : m < ‖z‖ := by
  have h2 : m ^ 2 < ‖z‖ ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hm, h2]
theorem sep_01 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc1‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_02 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc2‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_03 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_04 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_05 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_12 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc2‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_13 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_14 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_15 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_23 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_24 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_25 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_34 : (2 / 10 ^ 6 : ℝ) < ‖vc3 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc3 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_35 : (2 / 10 ^ 6 : ℝ) < ‖vc3 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc3 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem sep_45 : (2 / 10 ^ 6 : ℝ) < ‖vc4 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc4 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num
theorem zc0_mem : ‖zc0 - vc0‖ ≤ 1 / 1000000 := by
  have h := crit_loc_0.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc0_root : (Polynomial.derivative Q).eval zc0 = 0 :=
  crit_loc_0.choose_spec.1.2
theorem zc1_mem : ‖zc1 - vc1‖ ≤ 1 / 1000000 := by
  have h := crit_loc_1.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc1_root : (Polynomial.derivative Q).eval zc1 = 0 :=
  crit_loc_1.choose_spec.1.2
theorem zc2_mem : ‖zc2 - vc2‖ ≤ 1 / 1000000 := by
  have h := crit_loc_2.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc2_root : (Polynomial.derivative Q).eval zc2 = 0 :=
  crit_loc_2.choose_spec.1.2
theorem zc3_mem : ‖zc3 - vc3‖ ≤ 1 / 1000000 := by
  have h := crit_loc_3.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc3_root : (Polynomial.derivative Q).eval zc3 = 0 :=
  crit_loc_3.choose_spec.1.2
theorem zc4_mem : ‖zc4 - vc4‖ ≤ 1 / 1000000 := by
  have h := crit_loc_4.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc4_root : (Polynomial.derivative Q).eval zc4 = 0 :=
  crit_loc_4.choose_spec.1.2
theorem zc5_mem : ‖zc5 - vc5‖ ≤ 1 / 1000000 := by
  have h := crit_loc_5.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc5_root : (Polynomial.derivative Q).eval zc5 = 0 :=
  crit_loc_5.choose_spec.1.2
theorem rho_eps_ne_zero : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zero eps_ne_zero
theorem ne_of_disks {v1 v2 z1 z2 : ℂ} {rr : ℝ}
    (h1 : ‖z1 - v1‖ ≤ rr) (h2 : ‖z2 - v2‖ ≤ rr) (hsep : 2 * rr < ‖v1 - v2‖) : z1 ≠ z2 := by
  intro h
  subst h
  have hcalc : ‖v1 - v2‖ ≤ 2 * rr := by
    have he : v1 - v2 = (z1 - v2) - (z1 - v1) := by ring
    rw [he]
    calc ‖(z1 - v2) - (z1 - v1)‖ ≤ ‖z1 - v2‖ + ‖z1 - v1‖ := norm_sub_le _ _
      _ ≤ rr + rr := by linarith
      _ = 2 * rr := by ring
  linarith
theorem cf0_root : (Polynomial.derivative f).IsRoot cf0 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc0) = 0 := by
    rw [derivative_f_eval_rho_eps, zc0_root, mul_zero]
  exact h
theorem cf1_root : (Polynomial.derivative f).IsRoot cf1 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc1) = 0 := by
    rw [derivative_f_eval_rho_eps, zc1_root, mul_zero]
  exact h
theorem cf2_root : (Polynomial.derivative f).IsRoot cf2 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc2) = 0 := by
    rw [derivative_f_eval_rho_eps, zc2_root, mul_zero]
  exact h
theorem cf3_root : (Polynomial.derivative f).IsRoot cf3 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc3) = 0 := by
    rw [derivative_f_eval_rho_eps, zc3_root, mul_zero]
  exact h
theorem cf4_root : (Polynomial.derivative f).IsRoot cf4 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc4) = 0 := by
    rw [derivative_f_eval_rho_eps, zc4_root, mul_zero]
  exact h
theorem cf5_root : (Polynomial.derivative f).IsRoot cf5 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc5) = 0 := by
    rw [derivative_f_eval_rho_eps, zc5_root, mul_zero]
  exact h
theorem cfne01 : cf0 ≠ cf1 := by
  intro h
  exact ne_of_disks zc0_mem zc1_mem (by have hs := sep_01; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne02 : cf0 ≠ cf2 := by
  intro h
  exact ne_of_disks zc0_mem zc2_mem (by have hs := sep_02; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne03 : cf0 ≠ cf3 := by
  intro h
  exact ne_of_disks zc0_mem zc3_mem (by have hs := sep_03; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne04 : cf0 ≠ cf4 := by
  intro h
  exact ne_of_disks zc0_mem zc4_mem (by have hs := sep_04; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne05 : cf0 ≠ cf5 := by
  intro h
  exact ne_of_disks zc0_mem zc5_mem (by have hs := sep_05; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne12 : cf1 ≠ cf2 := by
  intro h
  exact ne_of_disks zc1_mem zc2_mem (by have hs := sep_12; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne13 : cf1 ≠ cf3 := by
  intro h
  exact ne_of_disks zc1_mem zc3_mem (by have hs := sep_13; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne14 : cf1 ≠ cf4 := by
  intro h
  exact ne_of_disks zc1_mem zc4_mem (by have hs := sep_14; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne15 : cf1 ≠ cf5 := by
  intro h
  exact ne_of_disks zc1_mem zc5_mem (by have hs := sep_15; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne23 : cf2 ≠ cf3 := by
  intro h
  exact ne_of_disks zc2_mem zc3_mem (by have hs := sep_23; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne24 : cf2 ≠ cf4 := by
  intro h
  exact ne_of_disks zc2_mem zc4_mem (by have hs := sep_24; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne25 : cf2 ≠ cf5 := by
  intro h
  exact ne_of_disks zc2_mem zc5_mem (by have hs := sep_25; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne34 : cf3 ≠ cf4 := by
  intro h
  exact ne_of_disks zc3_mem zc4_mem (by have hs := sep_34; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne35 : cf3 ≠ cf5 := by
  intro h
  exact ne_of_disks zc3_mem zc5_mem (by have hs := sep_35; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem cfne45 : cf4 ≠ cf5 := by
  intro h
  exact ne_of_disks zc4_mem zc5_mem (by have hs := sep_45; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)
theorem critMul_card : Multiset.card critMul = 6 := by decide +kernel
theorem critMul_nodup : critMul.Nodup := by
  simp only [critMul, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, not_or]
  refine ⟨⟨cfne01, cfne02, cfne03, cfne04, cfne05⟩, ⟨cfne12, cfne13, cfne14, cfne15⟩,
    ⟨cfne23, cfne24, cfne25⟩, ⟨cfne34, cfne35⟩, cfne45, ?_⟩
  trivial
theorem critMul_root : ∀ z ∈ critMul, (Polynomial.derivative f).IsRoot z := by
  intro z hz
  simp only [critMul, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hz
  rcases hz with h | h | h | h | h | h <;> subst h
  · exact cf0_root
  · exact cf1_root
  · exact cf2_root
  · exact cf3_root
  · exact cf4_root
  · exact cf5_root
theorem derivative_f_ne_zero : Polynomial.derivative f ≠ 0 := by
  intro h
  have hd := derivative_f_natDegree
  rw [h] at hd
  simp at hd
theorem derivative_f_roots_eq : (Polynomial.derivative f).roots = critMul := by
  have hsub : critMul ⊆ (Polynomial.derivative f).roots := by
    intro z hz
    exact (Polynomial.mem_roots derivative_f_ne_zero).mpr (critMul_root z hz)
  have hle : critMul ≤ (Polynomial.derivative f).roots :=
    (Multiset.le_iff_subset critMul_nodup).mpr hsub
  obtain ⟨m, hm⟩ := Multiset.le_iff_exists_add.mp hle
  have hdeg := Polynomial.card_roots' (Polynomial.derivative f)
  rw [derivative_f_natDegree, hm, Multiset.card_add, critMul_card] at hdeg
  have hm0 : Multiset.card m = 0 := by omega
  rw [hm, Multiset.card_eq_zero.mp hm0, add_zero]
theorem derivative_f_roots_nodup : (Polynomial.derivative f).roots.Nodup := by
  rw [derivative_f_roots_eq]; exact critMul_nodup
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : Polynomial.rootMultiplicity zs (Polynomial.derivative f) = 1 :=
  rootMultiplicity_eq_one_of_nodup derivative_f_ne_zero derivative_f_roots_nodup zs_crit
