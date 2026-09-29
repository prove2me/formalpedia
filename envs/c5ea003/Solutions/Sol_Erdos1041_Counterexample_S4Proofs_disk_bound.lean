-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.disk_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:22:52.793106+00:00
-- url     : https://prove2.me/submissions/63e4f54f-9207-4400-966e-aa55cebcfd53

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_taylor
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT7_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT3_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT4_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT5_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT6_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_f_eval_rho_eps
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT2_zc2_lower
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_shiftQuad_spec
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_zs_crit
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
theorem zc2_mem : ‖zc2 - vc2‖ ≤ 1 / 1000000 := by
  have h := crit_loc_2.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
theorem zc2_root : (Polynomial.derivative Q).eval zc2 = 0 :=
  crit_loc_2.choose_spec.1.2
theorem rho_eps_ne_zero : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zero eps_ne_zero
theorem qT1_eq_derivative (v : ℂ) : qT1 v = (Polynomial.derivative Q).eval v := by
  rw [derivative_Q_eval']
  unfold qT1 qq1 qq2 qq3 qq4 qq5 qq6 qq7 qp0 qp1 qp2 qp3 qp4 qp5 qp6
  ring
theorem qT1_zc2 : qT1 zc2 = 0 := by rw [qT1_eq_derivative]; exact zc2_root
theorem qT_shift3 (v τ : ℂ) : qT3 (v + τ)
    = qT3 v + (4 * qT4 v) * τ + (10 * qT5 v) * τ ^ 2 + (20 * qT6 v) * τ ^ 3
      + (35 * qT7) * τ ^ 4 := by
  unfold qT3 qT4 qT5 qT6 qT7; ring
theorem qT_shift4 (v τ : ℂ) : qT4 (v + τ)
    = qT4 v + (5 * qT5 v) * τ + (15 * qT6 v) * τ ^ 2 + (35 * qT7) * τ ^ 3 := by
  unfold qT4 qT5 qT6 qT7; ring
theorem qT_shift5 (v τ : ℂ) : qT5 (v + τ)
    = qT5 v + (6 * qT6 v) * τ + (21 * qT7) * τ ^ 2 := by
  unfold qT5 qT6 qT7; ring
theorem qT_shift6 (v τ : ℂ) : qT6 (v + τ) = qT6 v + (7 * qT7) * τ := by
  unfold qT6 qT7; ring
theorem tau_exists : ∃ τ : ℂ, ‖τ‖ ≤ 1 / 1000000 ∧ zc2 = vc2 + τ :=
  ⟨zc2 - vc2, zc2_mem, by ring⟩
theorem norm_shift_bound {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 1000000) {d : ℂ} {n : ℝ}
    (hd : ‖d‖ ≤ n) (k : ℕ) : ‖d * τ ^ k‖ ≤ n * (1 / 1000000 : ℝ) ^ k := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul hd (pow_le_pow_left₀ (norm_nonneg _) hτ k) (by positivity)
    (le_trans (norm_nonneg _) hd)
theorem norm_const_mul {c : ℂ} {d : ℂ} {m n : ℝ} (hc : ‖c‖ = m) (hm : 0 ≤ m)
    (hd : ‖d‖ ≤ n) : ‖c * d‖ ≤ m * n := by
  rw [norm_mul, hc]
  exact mul_le_mul_of_nonneg_left hd hm
theorem qT3_zc2_bound : ‖qT3 zc2‖ ≤ (189865523 / 1000000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift3]
  have b4 : ‖(4 : ℂ) * qT4 vc2‖ ≤ 4 * (19528067 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT4_vc2_bound
  have b5 : ‖(10 : ℂ) * qT5 vc2‖ ≤ 10 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(20 : ℂ) * qT6 vc2‖ ≤ 20 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(35 : ℂ) * qT7‖ ≤ 35 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t4 := norm_shift_bound hτ b4 1
  have t5 := norm_shift_bound hτ b5 2
  have t6 := norm_shift_bound hτ b6 3
  have t7 := norm_shift_bound hτ b7 4
  have htri : ‖qT3 vc2 + (4 * qT4 vc2) * τ + (10 * qT5 vc2) * τ ^ 2 + (20 * qT6 vc2) * τ ^ 3
      + (35 * qT7) * τ ^ 4‖
      ≤ ‖qT3 vc2‖ + ‖(4 * qT4 vc2) * τ‖ + ‖(10 * qT5 vc2) * τ ^ 2‖
        + ‖(20 * qT6 vc2) * τ ^ 3‖ + ‖(35 * qT7) * τ ^ 4‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t4 t5 t6 t7
  linarith [htri, qT3_vc2_bound, t4, t5, t6, t7]
theorem qT4_zc2_bound : ‖qT4 zc2‖ ≤ (19528139 / 1000000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift4]
  have b5 : ‖(5 : ℂ) * qT5 vc2‖ ≤ 5 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(15 : ℂ) * qT6 vc2‖ ≤ 15 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(35 : ℂ) * qT7‖ ≤ 35 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t5 := norm_shift_bound hτ b5 1
  have t6 := norm_shift_bound hτ b6 2
  have t7 := norm_shift_bound hτ b7 3
  have htri : ‖qT4 vc2 + (5 * qT5 vc2) * τ + (15 * qT6 vc2) * τ ^ 2 + (35 * qT7) * τ ^ 3‖
      ≤ ‖qT4 vc2‖ + ‖(5 * qT5 vc2) * τ‖ + ‖(15 * qT6 vc2) * τ ^ 2‖ + ‖(35 * qT7) * τ ^ 3‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t5 t6 t7
  linarith [htri, qT4_vc2_bound, t5, t6, t7]
theorem qT5_zc2_bound : ‖qT5 zc2‖ ≤ (5693 / 400 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift5]
  have b6 : ‖(6 : ℂ) * qT6 vc2‖ ≤ 6 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(21 : ℂ) * qT7‖ ≤ 21 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t6 := norm_shift_bound hτ b6 1
  have t7 := norm_shift_bound hτ b7 2
  have htri : ‖qT5 vc2 + (6 * qT6 vc2) * τ + (21 * qT7) * τ ^ 2‖
      ≤ ‖qT5 vc2‖ + ‖(6 * qT6 vc2) * τ‖ + ‖(21 * qT7) * τ ^ 2‖ :=
    le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t6 t7
  linarith [htri, qT5_vc2_bound, t6, t7]
theorem qT6_zc2_bound : ‖qT6 zc2‖ ≤ (288137 / 50000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift6]
  have b7 : ‖(7 : ℂ) * qT7‖ ≤ 7 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t7 := norm_shift_bound hτ b7 1
  have htri : ‖qT6 vc2 + (7 * qT7) * τ‖ ≤ ‖qT6 vc2‖ + ‖(7 * qT7) * τ‖ := norm_add_le _ _
  norm_num [norm_mul, norm_pow] at htri t7
  linarith [htri, qT6_vc2_bound, t7]
theorem Apoly_eval (z : ℂ) : Apoly.eval z
    = qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5
      + qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
      + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
      + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
      + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4
      + qT7 * z ^ 5 := by
  simp only [Apoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  try ring
theorem Q_eval_zc2 : Q.eval zc2 = qT0 zc2 := by
  have h := Q_taylor zc2 0
  simpa using h
theorem f_shift_scaled (t : ℂ) :
    f.eval (zs + (ρ : ℂ) * (ε : ℂ) * t) - f.eval zs
      = Apoly.eval ((ρ : ℂ) * (ε : ℂ) * t) * ((ρ : ℂ) * (ε : ℂ) * t) ^ 2 := by
  have h1 : zs + (ρ : ℂ) * (ε : ℂ) * t = (ρ : ℂ) * (ε : ℂ) * (zc2 + t) := by
    unfold zs; ring
  have h2 : zs = (ρ : ℂ) * (ε : ℂ) * zc2 := rfl
  rw [h1, f_eval_rho_eps, h2, f_eval_rho_eps, Q_taylor zc2 t, Q_eval_zc2, qT1_zc2,
    Apoly_eval]
  ring
theorem f_shift (z : ℂ) :
    f.eval (zs + z) - f.eval zs = Apoly.eval z * z ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, z = (ρ : ℂ) * (ε : ℂ) * t := by
    refine ⟨z / ((ρ : ℂ) * (ε : ℂ)), ?_⟩
    rw [mul_comm ((ρ : ℂ) * (ε : ℂ)) (z / ((ρ : ℂ) * (ε : ℂ))),
      div_mul_cancel₀ z rho_eps_ne_zero]
  exact f_shift_scaled t
theorem shiftQuad_eq : shiftQuad f zs = Apoly := by
  have hmul : (shiftQuad f zs) * Polynomial.X ^ 2 = Apoly * Polynomial.X ^ 2 := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [shiftQuad_spec f zs zs_crit z, f_shift z]
  exact mul_right_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) hmul
theorem aHat_norm : ‖aHat‖ = ‖qT2 zc2‖ * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
  unfold aHat
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ratCast, Complex.norm_ratCast,
    abs_of_pos rho_pos, abs_of_pos eps_pos]
theorem aHat_lower : 180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ := by
  rw [aHat_norm]
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  nlinarith [qT2_zc2_lower, h1, h2, mul_pos h1 h2]
theorem aHat_ne_zero : aHat ≠ 0 := by
  intro h
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  have := aHat_lower
  rw [h, norm_zero] at this
  nlinarith [this, mul_pos h1 h2]
theorem term_bound {n : ℝ} (hn : 0 ≤ n) {m k : ℕ} (hmk : m + k = 5) {Z : ℝ}
    (hZ : 0 ≤ Z) (hz : Z ≤ (ρ : ℝ) * (ε : ℝ) / 10) :
    n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * Z ^ k ≤ n * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ k := by
  have h1 : Z ^ k ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ k := pow_le_pow_left₀ hZ hz k
  have h2 : ((ρ : ℝ) * (ε : ℝ) / 10) ^ k = (ρ : ℝ) ^ k * (ε : ℝ) ^ k / 10 ^ k := by
    rw [div_pow, mul_pow]
  have h3 : (0 : ℝ) ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m :=
    mul_nonneg (mul_nonneg hn (pow_pos rho_pos m).le) (pow_pos eps_pos m).le
  calc n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * Z ^ k
      ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * ((ρ : ℝ) ^ k * (ε : ℝ) ^ k / 10 ^ k) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 h3
    _ = n * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ k := by
        rw [← hmk]; ring
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution (z : ℂ) (hz : ‖z‖ ≤ (ρ : ℝ) * (ε : ℝ) / 10) :
    ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4 := by
  have hr : (0 : ℝ) < (ρ : ℝ) := rho_pos
  have he : (0 : ℝ) < (ε : ℝ) := eps_pos
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hrw : (shiftQuad f zs).eval z / aHat - 1 = (Apoly.eval z - aHat) / aHat := by
    rw [shiftQuad_eq, sub_div, div_self aHat_ne_zero]
  have hnum : Apoly.eval z - aHat
      = qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
        + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
        + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
        + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4
        + qT7 * z ^ 5 := by
    rw [Apoly_eval]; unfold aHat; ring
  have hb : ∀ (d : ℂ) (n : ℝ) (m k : ℕ), ‖d‖ ≤ n →
      ‖d * (ρ : ℂ) ^ m * (ε : ℂ) ^ m * z ^ k‖ ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * ‖z‖ ^ k := by
    intro d n m k hd
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      Complex.norm_ratCast, Complex.norm_ratCast, abs_of_pos rho_pos, abs_of_pos eps_pos]
    have hn : 0 ≤ n := le_trans (norm_nonneg _) hd
    have := mul_le_mul_of_nonneg_right hd (le_of_lt (pow_pos rho_pos m))
    have h2 := mul_le_mul_of_nonneg_right this (le_of_lt (pow_pos eps_pos m))
    exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hzn k)
  have t3 := hb (qT3 zc2) (189865523 / 1000000) 4 1 qT3_zc2_bound
  have t4 := hb (qT4 zc2) (19528139 / 1000000) 3 2 qT4_zc2_bound
  have t5 := hb (qT5 zc2) (5693 / 400) 2 3 qT5_zc2_bound
  have t6 := hb (qT6 zc2) (288137 / 50000) 1 4 qT6_zc2_bound
  simp only [pow_one] at t3 t6
  have t7 : ‖qT7 * z ^ 5‖ ≤ 1 * ‖z‖ ^ 5 := by
    rw [norm_mul, norm_pow]
    have : ‖qT7‖ ≤ (1 : ℝ) := qT7_bound
    nlinarith [this, pow_nonneg hzn 5]
  have htri : ‖qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
      + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
      + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
      + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4 + qT7 * z ^ 5‖
      ≤ ‖qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z‖
        + ‖qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2‖
        + ‖qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3‖
        + ‖qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4‖ + ‖qT7 * z ^ 5‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have hz1 : ‖z‖ ≤ (ρ : ℝ) * (ε : ℝ) / 10 := hz
  have hpow : ∀ k : ℕ, ‖z‖ ^ k ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ k := fun k =>
    pow_le_pow_left₀ hzn hz1 k
  have hkey : ‖Apoly.eval z - aHat‖ ≤ (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
    rw [hnum]
    have s3 := term_bound (n := 189865523 / 1000000) (by norm_num) (m := 4) (k := 1)
      (by norm_num) hzn hz1
    have s4 := term_bound (n := 19528139 / 1000000) (by norm_num) (m := 3) (k := 2)
      (by norm_num) hzn hz1
    have s5 := term_bound (n := 5693 / 400) (by norm_num) (m := 2) (k := 3)
      (by norm_num) hzn hz1
    have s6 := term_bound (n := 288137 / 50000) (by norm_num) (m := 1) (k := 4)
      (by norm_num) hzn hz1
    have s7 := term_bound (n := 1) (by norm_num) (m := 0) (k := 5)
      (by norm_num) hzn hz1
    simp only [pow_one, pow_zero, mul_one, one_mul] at s3 s4 s5 s6 s7
    have hp5 : (0 : ℝ) < (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 :=
      mul_pos (pow_pos rho_pos 5) (pow_pos eps_pos 5)
    have hnum5 : (189865523 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 1
        + (19528139 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 2
        + (5693 / 400 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 3
        + (288137 / 50000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 4
        + (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 5
        ≤ (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
      nlinarith [hp5]
    linarith [htri, t3, t4, t5, t6, t7, s3, s4, s5, s6, s7, hnum5]
  have hq : (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ / 4 := by
    rw [aHat_norm]
    have hp5 : (0 : ℝ) < (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 :=
      mul_pos (pow_pos rho_pos 5) (pow_pos eps_pos 5)
    nlinarith [qT2_zc2_lower, hp5]
  have hanz : (0 : ℝ) < ‖aHat‖ := norm_pos_iff.mpr aHat_ne_zero
  rw [hrw, norm_div, div_le_iff₀ hanz]
  linarith [hkey, hq]
