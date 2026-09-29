-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.delta_small
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:06:46.708014+00:00
-- url     : https://prove2.me/submissions/37c7038e-99c8-4c47-88de-a29c67892c76

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
theorem norm_le_of_normSq_le {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : Complex.normSq z ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem Qd_taylor (δ : ℂ) :
    Qd (wq + δ) = hc1 + 2 * hc2 * δ + 3 * hc3 * δ ^ 2 + 4 * hc4 * δ ^ 3 + 5 * hc5 * δ ^ 4
      + 6 * hc6 * δ ^ 5 + 7 * δ ^ 6 := by
  simp only [Qd, hc1, hc2, hc3, hc4, hc5, hc6]
  ring
theorem norm_ge_of_le_normSq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : r ^ 2 ≤ Complex.normSq z) :
    r ≤ ‖z‖ := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem norm_hc6 : ‖hc6‖ ≤ 6 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc6, wq, p6, Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im])
theorem norm_hc5 : ‖hc5‖ ≤ 15 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc5, wq, p5, p6, Complex.normSq_apply, pow_succ, Complex.mul_re,
      Complex.mul_im])
theorem norm_hc4 : ‖hc4‖ ≤ 20 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc4, wq, p4, p5, p6, Complex.normSq_apply, pow_succ, Complex.mul_re,
      Complex.mul_im])
theorem norm_hc3 : ‖hc3‖ ≤ 190 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc3, wq, p3, p4, p5, p6, Complex.normSq_apply, pow_succ, Complex.mul_re,
      Complex.mul_im])
theorem norm_hc2_ge : (189 : ℝ) ≤ ‖hc2‖ :=
  norm_ge_of_le_normSq (by norm_num)
    (by norm_num [hc2, wq, p2, p3, p4, p5, p6, Complex.normSq_apply, pow_succ, Complex.mul_re,
      Complex.mul_im])
theorem norm_hc1 : ‖hc1‖ ≤ 1 / 10 ^ 38 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc1, wq, p1, p2, p3, p4, p5, p6, Complex.normSq_apply, pow_succ,
      Complex.mul_re, Complex.mul_im])
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (w : ℂ) (hQd : Qd w = 0) (hw : ‖w - wq‖ ≤ 1 / 500) :
    ‖w - wq‖ ≤ 1 / 10 ^ 8 := by
  have hwe : w = wq + (w - wq) := by ring
  rw [hwe, Qd_taylor] at hQd
  have hd0 : (0:ℝ) ≤ ‖w - wq‖ := norm_nonneg _
  have key : 2 * hc2 * (w - wq) = -(hc1 + 3 * hc3 * (w - wq) ^ 2 + 4 * hc4 * (w - wq) ^ 3
      + 5 * hc5 * (w - wq) ^ 4 + 6 * hc6 * (w - wq) ^ 5 + 7 * (w - wq) ^ 6) := by
    linear_combination hQd
  have hlhs : ‖2 * hc2 * (w - wq)‖ = 2 * ‖hc2‖ * ‖w - wq‖ := by
    rw [norm_mul, norm_mul]
    norm_num
  have hd2 : ‖w - wq‖ ^ 2 ≤ (1/500 : ℝ) * ‖w - wq‖ := by nlinarith
  have hd3 : ‖w - wq‖ ^ 3 ≤ (1/500 : ℝ) ^ 2 * ‖w - wq‖ := by nlinarith [hd2, sq_nonneg ‖w - wq‖]
  have hd4 : ‖w - wq‖ ^ 4 ≤ (1/500 : ℝ) ^ 3 * ‖w - wq‖ := by
    nlinarith [hd3, pow_nonneg hd0 3]
  have hd5 : ‖w - wq‖ ^ 5 ≤ (1/500 : ℝ) ^ 4 * ‖w - wq‖ := by
    nlinarith [hd4, pow_nonneg hd0 4]
  have hd6 : ‖w - wq‖ ^ 6 ≤ (1/500 : ℝ) ^ 5 * ‖w - wq‖ := by
    nlinarith [hd5, pow_nonneg hd0 5]
  have hmul : ∀ (z : ℂ) (U r : ℝ) (k : ℕ), ‖z‖ ≤ U → 0 ≤ U →
      ‖w - wq‖ ^ k ≤ r * ‖w - wq‖ → 0 ≤ r →
      ‖z * (w - wq) ^ k‖ ≤ U * (r * ‖w - wq‖) := by
    intro z U r k hU hU0 hr hr0
    rw [norm_mul, norm_pow]
    exact mul_le_mul hU hr (by positivity) hU0
  have c3 : ‖3 * hc3 * (w - wq) ^ 2‖ ≤ 570 * ((1/500:ℝ) * ‖w - wq‖) := by
    have h : ‖(3:ℂ) * hc3‖ ≤ 570 := by
      rw [norm_mul]; norm_num; linarith [norm_hc3]
    simpa [mul_assoc] using hmul ((3:ℂ) * hc3) 570 (1/500) 2 h (by norm_num) hd2 (by norm_num)
  have c4 : ‖4 * hc4 * (w - wq) ^ 3‖ ≤ 80 * ((1/500:ℝ) ^ 2 * ‖w - wq‖) := by
    have h : ‖(4:ℂ) * hc4‖ ≤ 80 := by
      rw [norm_mul]; norm_num; linarith [norm_hc4]
    simpa [mul_assoc] using hmul ((4:ℂ) * hc4) 80 ((1/500)^2) 3 h (by norm_num) hd3 (by norm_num)
  have c5 : ‖5 * hc5 * (w - wq) ^ 4‖ ≤ 75 * ((1/500:ℝ) ^ 3 * ‖w - wq‖) := by
    have h : ‖(5:ℂ) * hc5‖ ≤ 75 := by
      rw [norm_mul]; norm_num; linarith [norm_hc5]
    simpa [mul_assoc] using hmul ((5:ℂ) * hc5) 75 ((1/500)^3) 4 h (by norm_num) hd4 (by norm_num)
  have c6 : ‖6 * hc6 * (w - wq) ^ 5‖ ≤ 36 * ((1/500:ℝ) ^ 4 * ‖w - wq‖) := by
    have h : ‖(6:ℂ) * hc6‖ ≤ 36 := by
      rw [norm_mul]; norm_num; linarith [norm_hc6]
    simpa [mul_assoc] using hmul ((6:ℂ) * hc6) 36 ((1/500)^4) 5 h (by norm_num) hd5 (by norm_num)
  have c7 : ‖(7:ℂ) * (w - wq) ^ 6‖ ≤ 7 * ((1/500:ℝ) ^ 5 * ‖w - wq‖) := by
    rw [norm_mul, norm_pow]
    have h7 : ‖(7:ℂ)‖ = 7 := by norm_num
    rw [h7]
    nlinarith [hd6, hd0]
  have t1 := norm_add_le (hc1 + 3 * hc3 * (w - wq) ^ 2 + 4 * hc4 * (w - wq) ^ 3
    + 5 * hc5 * (w - wq) ^ 4 + 6 * hc6 * (w - wq) ^ 5) ((7:ℂ) * (w - wq) ^ 6)
  have t2 := norm_add_le (hc1 + 3 * hc3 * (w - wq) ^ 2 + 4 * hc4 * (w - wq) ^ 3
    + 5 * hc5 * (w - wq) ^ 4) (6 * hc6 * (w - wq) ^ 5)
  have t3 := norm_add_le (hc1 + 3 * hc3 * (w - wq) ^ 2 + 4 * hc4 * (w - wq) ^ 3)
    (5 * hc5 * (w - wq) ^ 4)
  have t4 := norm_add_le (hc1 + 3 * hc3 * (w - wq) ^ 2) (4 * hc4 * (w - wq) ^ 3)
  have t5 := norm_add_le hc1 (3 * hc3 * (w - wq) ^ 2)
  have hkey : ‖2 * hc2 * (w - wq)‖ = ‖hc1 + 3 * hc3 * (w - wq) ^ 2 + 4 * hc4 * (w - wq) ^ 3
      + 5 * hc5 * (w - wq) ^ 4 + 6 * hc6 * (w - wq) ^ 5 + 7 * (w - wq) ^ 6‖ := by
    rw [key, norm_neg]
  have hbig : (378:ℝ) * ‖w - wq‖ ≤ 1 / 10 ^ 38 + (1141/1000 : ℝ) * ‖w - wq‖ := by
    have hL : (378:ℝ) * ‖w - wq‖ ≤ ‖2 * hc2 * (w - wq)‖ := by
      rw [hlhs]
      nlinarith [norm_hc2_ge, hd0]
    have hnum : (570:ℝ) * ((1/500:ℝ) * ‖w - wq‖) + 80 * ((1/500:ℝ) ^ 2 * ‖w - wq‖)
        + 75 * ((1/500:ℝ) ^ 3 * ‖w - wq‖) + 36 * ((1/500:ℝ) ^ 4 * ‖w - wq‖)
        + 7 * ((1/500:ℝ) ^ 5 * ‖w - wq‖) ≤ (1141/1000 : ℝ) * ‖w - wq‖ := by
      nlinarith [hd0]
    rw [hkey] at hL
    linarith [norm_hc1]
  linarith
