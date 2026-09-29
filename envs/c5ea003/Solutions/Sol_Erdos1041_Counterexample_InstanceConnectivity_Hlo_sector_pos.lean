-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.Hlo_sector_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:06:32.888995+00:00
-- url     : https://prove2.me/submissions/e569c5e8-6ea1-4138-a423-eec8eba5f1fa

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
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (x u : ℂ) (hu : ‖u‖ = 1) (hu7 : u ^ 7 = 1)
    (hxu : ‖x - u‖ ≤ 1 / 10) (hx : ‖x‖ ≤ 101 / 100) :
    0 < Hlo (8 * x) := by
  have hn0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hpow : ∀ k : ℕ, ‖x‖ ^ k ≤ (101 / 100 : ℝ) ^ k := fun k => pow_le_pow_left₀ hn0 hx k
  -- the telescoping factorisation
  have hfac : x ^ 7 - 1 = (x - u) *
      (x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2 + x ^ 3 * u ^ 3 + x ^ 2 * u ^ 4 + x * u ^ 5 + u ^ 6) := by
    have h1 : (1 : ℂ) = u ^ 7 := hu7.symm
    rw [h1]; ring
  have e6 : ‖x ^ 6‖ = ‖x‖ ^ 6 := norm_pow x 6
  have e5 : ‖x ^ 5 * u‖ = ‖x‖ ^ 5 := by rw [norm_mul, norm_pow, hu, mul_one]
  have e4 : ‖x ^ 4 * u ^ 2‖ = ‖x‖ ^ 4 := by rw [norm_mul, norm_pow, norm_pow, hu, one_pow, mul_one]
  have e3 : ‖x ^ 3 * u ^ 3‖ = ‖x‖ ^ 3 := by rw [norm_mul, norm_pow, norm_pow, hu, one_pow, mul_one]
  have e2 : ‖x ^ 2 * u ^ 4‖ = ‖x‖ ^ 2 := by rw [norm_mul, norm_pow, norm_pow, hu, one_pow, mul_one]
  have e1 : ‖x * u ^ 5‖ = ‖x‖ := by rw [norm_mul, norm_pow, hu, one_pow, mul_one]
  have e0 : ‖u ^ 6‖ = 1 := by rw [norm_pow, hu, one_pow]
  have hsum : ‖x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2 + x ^ 3 * u ^ 3 + x ^ 2 * u ^ 4 + x * u ^ 5
      + u ^ 6‖ ≤ 7214 / 1000 := by
    have t1 := norm_add_le (x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2 + x ^ 3 * u ^ 3 + x ^ 2 * u ^ 4
      + x * u ^ 5) (u ^ 6)
    have t2 := norm_add_le (x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2 + x ^ 3 * u ^ 3 + x ^ 2 * u ^ 4)
      (x * u ^ 5)
    have t3 := norm_add_le (x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2 + x ^ 3 * u ^ 3) (x ^ 2 * u ^ 4)
    have t4 := norm_add_le (x ^ 6 + x ^ 5 * u + x ^ 4 * u ^ 2) (x ^ 3 * u ^ 3)
    have t5 := norm_add_le (x ^ 6 + x ^ 5 * u) (x ^ 4 * u ^ 2)
    have t6 := norm_add_le (x ^ 6) (x ^ 5 * u)
    have b6 := hpow 6; have b5 := hpow 5; have b4 := hpow 4
    have b3 := hpow 3; have b2 := hpow 2; have b1 := hpow 1
    have hb1 : ‖x‖ ^ 1 = ‖x‖ := pow_one _
    have : ((101:ℝ)/100) ^ 6 + (101/100:ℝ) ^ 5 + (101/100:ℝ) ^ 4 + (101/100:ℝ) ^ 3
        + (101/100:ℝ) ^ 2 + (101/100:ℝ) ^ 1 + 1 ≤ 7214 / 1000 := by norm_num
    linarith
  have hx7 : ‖x ^ 7 - 1‖ ≤ 7214 / 10000 := by
    rw [hfac, norm_mul]
    have := mul_le_mul hxu hsum (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1 / 10)
    linarith
  have hre7 : (2786 / 10000 : ℝ) ≤ (x ^ 7).re := by
    have h1 : |(x ^ 7 - 1).re| ≤ ‖x ^ 7 - 1‖ := Complex.abs_re_le_norm _
    have h2 : (x ^ 7 - 1).re = (x ^ 7).re - 1 := by simp
    rw [h2, abs_le] at h1
    linarith [h1.1, h1.2]
  -- the low-order tail
  have htk : ∀ (z : ℂ) (k : ℕ) (U : ℝ), ‖z‖ ≤ U → 0 ≤ U →
      ‖z * (8 * x) ^ k‖ ≤ U * 8 ^ k * (101 / 100 : ℝ) ^ k := by
    intro z k U hU hU0
    rw [norm_mul, norm_pow, norm_mul]
    have : ‖(8:ℂ)‖ = 8 := by simp
    rw [this, mul_pow]
    have h1 : ‖x‖ ^ k ≤ (101/100:ℝ) ^ k := hpow k
    have h2 : (0:ℝ) ≤ (8:ℝ) ^ k := by positivity
    calc ‖z‖ * (8 ^ k * ‖x‖ ^ k) ≤ U * (8 ^ k * (101/100:ℝ) ^ k) := by
          apply mul_le_mul hU (by nlinarith) (by positivity) hU0
      _ = U * 8 ^ k * (101/100:ℝ) ^ k := by ring
  have k1 := htk p1 1 720 norm_p1 (by norm_num)
  have k2 := htk p2 2 690 norm_p2 (by norm_num)
  have k3 := htk p3 3 206 norm_p3 (by norm_num)
  have k4 := htk p4 4 (1/10^9) norm_p4 (by norm_num)
  have k5 := htk p5 5 (1/10^30) norm_p5 (by norm_num)
  have k6 := htk p6 6 (1/10^55) norm_p6 (by norm_num)
  have htail : ‖p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4 + p3 * (8*x) ^ 3
      + p2 * (8*x) ^ 2 + p1 * (8*x)‖ ≤ 159534 := by
    have t1 := norm_add_le (p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4 + p3 * (8*x) ^ 3
      + p2 * (8*x) ^ 2) (p1 * (8*x))
    have t2 := norm_add_le (p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4 + p3 * (8*x) ^ 3)
      (p2 * (8*x) ^ 2)
    have t3 := norm_add_le (p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4) (p3 * (8*x) ^ 3)
    have t4 := norm_add_le (p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5) (p4 * (8*x) ^ 4)
    have t5 := norm_add_le (p6 * (8*x) ^ 6) (p5 * (8*x) ^ 5)
    have hp1 : ‖p1 * (8 * x)‖ ≤ 720 * 8 ^ 1 * (101/100:ℝ) ^ 1 := by
      simpa using k1
    have hnum : (720:ℝ) * 8 ^ 1 * (101/100:ℝ) ^ 1 + 690 * 8 ^ 2 * (101/100:ℝ) ^ 2
        + 206 * 8 ^ 3 * (101/100:ℝ) ^ 3 + (1/10^9 : ℝ) * 8 ^ 4 * (101/100:ℝ) ^ 4
        + (1/10^30 : ℝ) * 8 ^ 5 * (101/100:ℝ) ^ 5
        + (1/10^55 : ℝ) * 8 ^ 6 * (101/100:ℝ) ^ 6 ≤ 159534 := by norm_num
    linarith
  -- assemble
  have hQ : Q.eval (8 * x) = (8 * x) ^ 7 + (p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4
      + p3 * (8*x) ^ 3 + p2 * (8*x) ^ 2 + p1 * (8*x)) := by
    rw [Q_eval]; ring
  set T : ℂ := p6 * (8*x) ^ 6 + p5 * (8*x) ^ 5 + p4 * (8*x) ^ 4 + p3 * (8*x) ^ 3
    + p2 * (8*x) ^ 2 + p1 * (8*x) with hT
  have hbig : ((8 * x) ^ 7).re = 8 ^ 7 * (x ^ 7).re := by
    have h : (8 * x) ^ 7 = (((8:ℝ) ^ 7 : ℝ) : ℂ) * x ^ 7 := by push_cast; ring
    rw [h]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hReQ : (424732 : ℝ) ≤ (Q.eval (8 * x)).re := by
    have h1 : (Q.eval (8 * x)).re = ((8 * x) ^ 7).re + T.re := by rw [hQ]; simp
    have h2 : |T.re| ≤ ‖T‖ := Complex.abs_re_le_norm _
    rw [abs_le] at h2
    rw [h1, hbig]
    nlinarith [h2.1, htail, hre7]
  have hnormQ : ‖Q.eval (8 * x)‖ ≤ 2410000 := by
    have h1 : ‖Q.eval (8 * x)‖ ≤ ‖(8 * x) ^ 7‖ + ‖T‖ := by rw [hQ]; exact norm_add_le _ _
    have h2 : ‖(8 * x) ^ 7‖ = 8 ^ 7 * ‖x‖ ^ 7 := by
      rw [norm_pow, norm_mul]
      have : ‖(8:ℂ)‖ = 8 := by simp
      rw [this, mul_pow]
    have h3 : ‖x‖ ^ 7 ≤ (101/100:ℝ) ^ 7 := hpow 7
    have h4 : (8:ℝ) ^ 7 * (101/100:ℝ) ^ 7 + 159534 ≤ 2410000 := by norm_num
    nlinarith [htail]
  have hnsq : Complex.normSq (Q.eval (8 * x)) ≤ 2410000 ^ 2 := normSq_le_of_norm_le hnormQ
  have hHdef : Hlo (8 * x) = 7 * (ε:ℝ) + (Q.eval (8 * x)).re
      - (ε:ℝ) ^ 7 / 2 * Complex.normSq (Q.eval (8 * x)) := rfl
  have heps : (ε:ℝ) = 1 / 10 ^ 12 := by norm_num [ε, s]
  have hnsq0 : (0:ℝ) ≤ Complex.normSq (Q.eval (8 * x)) := Complex.normSq_nonneg _
  rw [hHdef, heps]
  nlinarith [hReQ, hnsq, hnsq0]
