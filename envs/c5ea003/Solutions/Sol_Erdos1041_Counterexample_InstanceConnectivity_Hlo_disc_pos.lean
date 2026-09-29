-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.Hlo_disc_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:06:21.987059+00:00
-- url     : https://prove2.me/submissions/9d468daa-ba3d-4eca-ab85-c54faa203b21

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
theorem Q_eval (w : ℂ) :
    Q.eval w = w ^ 7 + p6 * w ^ 6 + p5 * w ^ 5 + p4 * w ^ 4 + p3 * w ^ 3 + p2 * w ^ 2 + p1 * w := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num [a, b, c, A, B, Cconst, t, s, p1, p2, p3, p4, p5, p6, Complex.conj_ofNat]
  ring
theorem norm_le_of_normSq_le {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : Complex.normSq z ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem normSq_le_of_norm_le {z : ℂ} {r : ℝ} (h : ‖z‖ ≤ r) : Complex.normSq z ≤ r ^ 2 := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem Q_taylor (δ : ℂ) :
    Q.eval (wq + δ) = hc0 + hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3 + hc4 * δ ^ 4 + hc5 * δ ^ 5
      + hc6 * δ ^ 6 + δ ^ 7 := by
  rw [Q_eval]
  simp only [hc0, hc1, hc2, hc3, hc4, hc5, hc6]
  ring
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
theorem norm_hc2 : ‖hc2‖ ≤ 190 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc2, wq, p2, p3, p4, p5, p6, Complex.normSq_apply, pow_succ, Complex.mul_re,
      Complex.mul_im])
theorem norm_hc1 : ‖hc1‖ ≤ 1 / 10 ^ 38 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc1, wq, p1, p2, p3, p4, p5, p6, Complex.normSq_apply, pow_succ,
      Complex.mul_re, Complex.mul_im])
theorem norm_hc0 : ‖hc0‖ ≤ 240 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [hc0, wq, p1, p2, p3, p4, p5, p6, Complex.normSq_apply, pow_succ,
      Complex.mul_re, Complex.mul_im])
theorem re_hc0 : (355 / 10 ^ 8 : ℝ) ≤ hc0.re := by
  norm_num [hc0, wq, p1, p2, p3, p4, p5, p6, pow_succ, Complex.mul_re, Complex.mul_im]
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (δ : ℂ) (hδ : ‖δ‖ ≤ 1 / 10 ^ 8) : 0 < Hlo (wq + δ) := by
  have hd0 : (0:ℝ) ≤ ‖δ‖ := norm_nonneg δ
  have hdk : ∀ k : ℕ, ‖δ‖ ^ k ≤ (1 / 10 ^ 8 : ℝ) ^ k := fun k => pow_le_pow_left₀ hd0 hδ k
  have hmul : ∀ (z : ℂ) (U : ℝ) (k : ℕ), ‖z‖ ≤ U → 0 ≤ U →
      ‖z * δ ^ k‖ ≤ U * (1 / 10 ^ 8 : ℝ) ^ k := by
    intro z U k hU hU0
    rw [norm_mul, norm_pow]
    exact mul_le_mul hU (hdk k) (by positivity) hU0
  have m1 := hmul hc1 (1/10^38) 1 norm_hc1 (by norm_num)
  have m2 := hmul hc2 190 2 norm_hc2 (by norm_num)
  have m3' := hmul hc3 190 3 norm_hc3 (by norm_num)
  have m4 := hmul hc4 20 4 norm_hc4 (by norm_num)
  have m5 := hmul hc5 15 5 norm_hc5 (by norm_num)
  have m6 := hmul hc6 6 6 norm_hc6 (by norm_num)
  have m7 : ‖δ ^ 7‖ ≤ (1/10^8 : ℝ) ^ 7 := by rw [norm_pow]; exact hdk 7
  have hm1 : ‖hc1 * δ‖ ≤ (1/10^38 : ℝ) * (1/10^8 : ℝ) ^ 1 := by simpa using m1
  set T : ℂ := hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3 + hc4 * δ ^ 4 + hc5 * δ ^ 5 + hc6 * δ ^ 6
    + δ ^ 7 with hT
  have t1 := norm_add_le (hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3 + hc4 * δ ^ 4 + hc5 * δ ^ 5
    + hc6 * δ ^ 6) (δ ^ 7)
  have t2 := norm_add_le (hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3 + hc4 * δ ^ 4 + hc5 * δ ^ 5)
    (hc6 * δ ^ 6)
  have t3 := norm_add_le (hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3 + hc4 * δ ^ 4) (hc5 * δ ^ 5)
  have t4 := norm_add_le (hc1 * δ + hc2 * δ ^ 2 + hc3 * δ ^ 3) (hc4 * δ ^ 4)
  have t5 := norm_add_le (hc1 * δ + hc2 * δ ^ 2) (hc3 * δ ^ 3)
  have t6 := norm_add_le (hc1 * δ) (hc2 * δ ^ 2)
  have hnum : (1/10^38 : ℝ) * (1/10^8 : ℝ) ^ 1 + 190 * (1/10^8 : ℝ) ^ 2
      + 190 * (1/10^8 : ℝ) ^ 3 + 20 * (1/10^8 : ℝ) ^ 4 + 15 * (1/10^8 : ℝ) ^ 5
      + 6 * (1/10^8 : ℝ) ^ 6 + (1/10^8 : ℝ) ^ 7 ≤ 2 / 10 ^ 14 := by norm_num
  have hTb : ‖T‖ ≤ 2 / 10 ^ 14 := by rw [hT]; linarith
  have hQt : Q.eval (wq + δ) = hc0 + T := by rw [Q_taylor, hT]; ring
  have hreQ : (354 / 10 ^ 8 : ℝ) ≤ (Q.eval (wq + δ)).re := by
    have h1 : |T.re| ≤ ‖T‖ := Complex.abs_re_le_norm _
    rw [abs_le] at h1
    rw [hQt, Complex.add_re]
    linarith [re_hc0, h1.1, hTb]
  have hnQ : ‖Q.eval (wq + δ)‖ ≤ 241 := by
    rw [hQt]
    refine le_trans (norm_add_le _ _) ?_
    linarith [norm_hc0, hTb]
  have hnsq : Complex.normSq (Q.eval (wq + δ)) ≤ 241 ^ 2 := normSq_le_of_norm_le hnQ
  have hnsq0 : (0:ℝ) ≤ Complex.normSq (Q.eval (wq + δ)) := Complex.normSq_nonneg _
  have hHdef : Hlo (wq + δ) = 7 * (ε:ℝ) + (Q.eval (wq + δ)).re
      - (ε:ℝ) ^ 7 / 2 * Complex.normSq (Q.eval (wq + δ)) := rfl
  have heps : (ε:ℝ) = 1 / 10 ^ 12 := by norm_num [ε, s]
  rw [hHdef, heps]
  nlinarith [hreQ, hnsq, hnsq0]
