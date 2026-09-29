-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.qT2_zc2_lower
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:21:44.346677+00:00
-- url     : https://prove2.me/submissions/ca4d4e7f-a5c2-48ba-9a77-2b8c96bedf8a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT7_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT3_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT4_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT5_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT6_vc2_bound
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT2_vc2_lower
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
theorem qT_shift2 (v τ : ℂ) : qT2 (v + τ)
    = qT2 v + (3 * qT3 v) * τ + (6 * qT4 v) * τ ^ 2 + (10 * qT5 v) * τ ^ 3
      + (15 * qT6 v) * τ ^ 4 + (21 * qT7) * τ ^ 5 := by
  unfold qT2 qT3 qT4 qT5 qT6 qT7; ring
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
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : (23637591 / 125000 : ℝ) ≤ ‖qT2 zc2‖ := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift2]
  have b3 : ‖(3 : ℂ) * qT3 vc2‖ ≤ 3 * (47466361 / 250000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT3_vc2_bound
  have b4 : ‖(6 : ℂ) * qT4 vc2‖ ≤ 6 * (19528067 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT4_vc2_bound
  have b5 : ‖(10 : ℂ) * qT5 vc2‖ ≤ 10 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(15 : ℂ) * qT6 vc2‖ ≤ 15 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(21 : ℂ) * qT7‖ ≤ 21 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t3 := norm_shift_bound hτ b3 1
  have t4 := norm_shift_bound hτ b4 2
  have t5 := norm_shift_bound hτ b5 3
  have t6 := norm_shift_bound hτ b6 4
  have t7 := norm_shift_bound hτ b7 5
  have htri : ‖qT2 vc2 + (3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
      + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5‖
      ≥ ‖qT2 vc2‖ - (‖(3 * qT3 vc2) * τ‖ + ‖(6 * qT4 vc2) * τ ^ 2‖
        + ‖(10 * qT5 vc2) * τ ^ 3‖ + ‖(15 * qT6 vc2) * τ ^ 4‖ + ‖(21 * qT7) * τ ^ 5‖) := by
    have hsplit : qT2 vc2 + (3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5
        = qT2 vc2 + ((3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
          + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5) := by ring
    rw [hsplit]
    have hrest : ‖(3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5‖
        ≤ ‖(3 * qT3 vc2) * τ‖ + ‖(6 * qT4 vc2) * τ ^ 2‖ + ‖(10 * qT5 vc2) * τ ^ 3‖
          + ‖(15 * qT6 vc2) * τ ^ 4‖ + ‖(21 * qT7) * τ ^ 5‖ :=
      le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    have := norm_sub_norm_le (qT2 vc2)
      (-((3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5))
    simp only [sub_neg_eq_add, norm_neg] at this
    linarith [this, hrest]
  norm_num [norm_mul, norm_pow] at htri t3 t4 t5 t6 t7
  linarith [htri, qT2_vc2_lower, t3, t4, t5, t6, t7]
