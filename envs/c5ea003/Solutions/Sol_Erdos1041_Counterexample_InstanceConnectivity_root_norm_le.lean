-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.root_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:06:33.506882+00:00
-- url     : https://prove2.me/submissions/9a9357b3-5b5c-401d-8c31-79694ae1593d

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate

namespace Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem epsilon_pos : 0 < (ε : ℝ) := by
  norm_num [ε, s]
theorem F_eval (z : ℂ) :
    F.eval z = z ^ 7 - 1
      + (ε : ℂ) ^ 6 * p1 * z + (ε : ℂ) ^ 5 * p2 * z ^ 2 + (ε : ℂ) ^ 4 * p3 * z ^ 3
      + (ε : ℂ) ^ 3 * p4 * z ^ 4 + (ε : ℂ) ^ 2 * p5 * z ^ 5 + (ε : ℂ) * p6 * z ^ 6 := by
  simp only [F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num [a, b, c, A, B, Cconst, t, s, ε, p1, p2, p3, p4, p5, p6, Complex.conj_ofNat]
  ring
theorem norm_le_of_normSq_le {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : Complex.normSq z ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem norm_p1 : ‖p1‖ ≤ 720 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p1, Complex.normSq_apply])
theorem norm_p2 : ‖p2‖ ≤ 690 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p2, Complex.normSq_apply])
theorem norm_p3 : ‖p3‖ ≤ 206 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p3, Complex.normSq_apply])
theorem norm_p4 : ‖p4‖ ≤ 1 / 10 ^ 9 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p4, Complex.normSq_apply])
theorem norm_p5 : ‖p5‖ ≤ 1 / 10 ^ 30 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p5, Complex.normSq_apply])
theorem norm_p6 : ‖p6‖ ≤ 1 / 10 ^ 55 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p6, Complex.normSq_apply])
theorem eps_normC : ‖((ε : ℚ) : ℂ)‖ = (ε : ℝ) := by
  rw [Complex.norm_ratCast, abs_of_pos epsilon_pos]
theorem F_root_eq (z : ℂ) (hz : F.eval z = 0) :
    z ^ 7 = 1 - ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3
      + (ε:ℂ) ^ 3 * p4 * z ^ 4 + (ε:ℂ) ^ 2 * p5 * z ^ 5 + (ε:ℂ) * p6 * z ^ 6) := by
  have h := F_eval z
  rw [hz] at h
  linear_combination -h
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (z : ℂ) (hz : F.eval z = 0) : ‖z‖ ≤ 101 / 100 := by
  by_contra hcon
  push_neg at hcon
  have hr1 : (1 : ℝ) ≤ ‖z‖ := by linarith
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpk : ∀ k : ℕ, k ≤ 6 → ‖z‖ ^ k ≤ ‖z‖ ^ 6 := fun k hk => pow_le_pow_right₀ hr1 hk
  have key := F_root_eq z hz
  have hterm : ∀ (j : ℕ) (pk : ℂ) (U : ℝ) (k : ℕ), ‖pk‖ ≤ U → 0 ≤ U → k ≤ 6 →
      (ε:ℝ) ^ j * U ≤ 1 / 10 ^ 45 → ‖(ε:ℂ) ^ j * pk * z ^ k‖ ≤ (1 / 10 ^ 45) * ‖z‖ ^ 6 := by
    intro j pk U k hU hU0 hk hnum
    rw [norm_mul, norm_mul, norm_pow, eps_normC, norm_pow]
    have h1 : (ε:ℝ) ^ j * ‖pk‖ ≤ (ε:ℝ) ^ j * U := by
      have : (0:ℝ) ≤ (ε:ℝ) ^ j := pow_nonneg (le_of_lt epsilon_pos) j
      nlinarith
    have h2 : ‖z‖ ^ k ≤ ‖z‖ ^ 6 := hpk k hk
    have h3 : (0:ℝ) ≤ ‖z‖ ^ k := by positivity
    have h4 : (0:ℝ) ≤ (ε:ℝ) ^ j * ‖pk‖ := mul_nonneg (pow_nonneg (le_of_lt epsilon_pos) j) (norm_nonneg pk)
    nlinarith [norm_nonneg pk]
  have heps : (ε:ℝ) = 1 / 10 ^ 12 := by norm_num [ε, s]
  have b1 := hterm 6 p1 720 1 norm_p1 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have b2 := hterm 5 p2 690 2 norm_p2 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have b3 := hterm 4 p3 206 3 norm_p3 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have b4 := hterm 3 p4 (1/10^9) 4 norm_p4 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have b5 := hterm 2 p5 (1/10^30) 5 norm_p5 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have b6 := hterm 1 p6 (1/10^55) 6 norm_p6 (by norm_num) (by norm_num) (by rw [heps]; norm_num)
  have hb6 : ‖(ε:ℂ) * p6 * z ^ 6‖ ≤ (1 / 10 ^ 45) * ‖z‖ ^ 6 := by simpa using b6
  have t1 := norm_add_le ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3
    + (ε:ℂ) ^ 3 * p4 * z ^ 4 + (ε:ℂ) ^ 2 * p5 * z ^ 5) ((ε:ℂ) * p6 * z ^ 6)
  have t2 := norm_add_le ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3
    + (ε:ℂ) ^ 3 * p4 * z ^ 4) ((ε:ℂ) ^ 2 * p5 * z ^ 5)
  have t3 := norm_add_le ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3)
    ((ε:ℂ) ^ 3 * p4 * z ^ 4)
  have t4 := norm_add_le ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2) ((ε:ℂ) ^ 4 * p3 * z ^ 3)
  have t5 := norm_add_le ((ε:ℂ) ^ 6 * p1 * z) ((ε:ℂ) ^ 5 * p2 * z ^ 2)
  have hb1 : ‖(ε:ℂ) ^ 6 * p1 * z‖ ≤ (1 / 10 ^ 45) * ‖z‖ ^ 6 := by simpa using b1
  have hsum : ‖(ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3
      + (ε:ℂ) ^ 3 * p4 * z ^ 4 + (ε:ℂ) ^ 2 * p5 * z ^ 5 + (ε:ℂ) * p6 * z ^ 6‖
      ≤ 6 * (1 / 10 ^ 45) * ‖z‖ ^ 6 := by linarith
  have hz7 : ‖z‖ ^ 7 ≤ 1 + 6 * (1 / 10 ^ 45) * ‖z‖ ^ 6 := by
    have h1 : ‖z ^ 7‖ = ‖z‖ ^ 7 := norm_pow z 7
    have h2 : ‖z ^ 7‖ ≤ ‖(1:ℂ)‖ + ‖(ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2
        + (ε:ℂ) ^ 4 * p3 * z ^ 3 + (ε:ℂ) ^ 3 * p4 * z ^ 4 + (ε:ℂ) ^ 2 * p5 * z ^ 5
        + (ε:ℂ) * p6 * z ^ 6‖ := by
      rw [key]
      exact norm_sub_le _ _
    rw [h1] at h2
    simp only [norm_one] at h2
    linarith
  have hr6 : (101/100:ℝ) ^ 6 ≤ ‖z‖ ^ 6 := pow_le_pow_left₀ (by norm_num) (le_of_lt hcon) 6
  nlinarith [hz7, hr6, hcon]
