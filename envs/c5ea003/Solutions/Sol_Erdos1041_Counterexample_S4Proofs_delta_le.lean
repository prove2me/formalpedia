-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.delta_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:23:46.735108+00:00
-- url     : https://prove2.me/submissions/4c7ffcd4-017c-459d-9534-167af38e291a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pow7_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_K0_le
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_lt_one
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_var_vc2
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Hs_pos_vc2
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_one_sub_sq_norm_f_rho_eps
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT0_vc2_re_hi
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_zs_mem_omega
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
theorem Hs_le_on_disk {v : ℂ} {rr var reHi : ℝ}
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : (qT0 v).re ≤ reHi) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → Hs w ≤ reHi + var + 1 / 10 ^ 11 := by
  intro w hw
  have hv := hvar w hw
  have hrele : (Q.eval w).re - (qT0 v).re ≤ var := by
    have hb := Complex.abs_re_le_norm (Q.eval w - qT0 v)
    simp only [Complex.sub_re] at hb
    calc (Q.eval w).re - (qT0 v).re ≤ |(Q.eval w).re - (qT0 v).re| := le_abs_self _
      _ ≤ ‖Q.eval w - qT0 v‖ := hb
      _ ≤ var := hv
  have hquad : 0 ≤ ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) :=
    mul_nonneg (by linarith [eps_pow7_pos]) (Complex.normSq_nonneg _)
  unfold Hs
  linarith [K0_le, hrele, hre, hquad]
theorem Hs_zc2_pos : 0 < Hs zc2 := Hs_pos_vc2 zc2 zc2_mem
theorem Hs_zc2_le : Hs zc2 ≤ 3558 / 10 ^ 9 := by
  have h := Hs_le_on_disk Q_var_vc2 qT0_vc2_re_hi zc2 zc2_mem
  norm_num at h ⊢
  linarith
theorem norm_f_zs_lt_one : ‖f.eval ((ρ : ℂ) * (ε : ℂ) * zc2)‖ < 1 := zs_mem_omega
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : 1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) := by
  have hid := one_sub_sq_norm_f_rho_eps zc2
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * zc2))
  have hlt := norm_f_zs_lt_one
  have hstep : 1 - ‖f.eval ((ρ : ℂ) * (ε : ℂ) * zc2)‖
      ≤ 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs zc2 := by
    nlinarith [hid, hn, hlt]
  have hr7 : (0 : ℝ) < (ρ : ℝ) ^ 7 := pow_pos rho_pos 7
  have hr7le : (ρ : ℝ) ^ 7 ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have he7 : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7
  have hp : (ρ : ℝ) ^ 7 * Hs zc2 ≤ 3558 / 10 ^ 9 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (ρ : ℝ) ^ 7) Hs_zc2_pos.le,
      Hs_zc2_le]
  have h14 : (ρ : ℝ) ^ 14 = (ρ : ℝ) ^ 7 * (ρ : ℝ) ^ 7 := by ring
  have hfin : 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs zc2
      ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) := by
    rw [h14]
    nlinarith [hp, mul_pos hr7 he7, he7, hr7]
  unfold zs
  linarith [hstep, hfin]
