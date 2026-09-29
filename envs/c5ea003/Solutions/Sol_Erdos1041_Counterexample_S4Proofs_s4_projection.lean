-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.s4_projection
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:40:11.315512+00:00
-- url     : https://prove2.me/submissions/40884334-e9e1-4163-bdc4-92e88a0b0ce6

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_cayley_norm
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_realRoot_mem
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_norm_cayley_sub_le
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_3
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_6
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
theorem cayley3_near : ‖cayley (realRoot 3) - u 3‖ ≤ 1 / 500 := by
  have hx1 : (43812 / 10000 : ℝ) < realRoot 3 := (realRoot_mem 3).1
  have hx2 : realRoot 3 < (43813 / 10000 : ℝ) := (realRoot_mem 3).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  refine norm_cayley_sub_le (M := 1 / 200) (D := 20) (by norm_num)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by norm_num) (by nlinarith) (by norm_num)
theorem cayley6_near : ‖cayley (realRoot 6) - u 6‖ ≤ 1 / 100 := by
  have hx1 : (-4816 / 10000 : ℝ) < realRoot 6 := (realRoot_mem 6).1
  have hx2 : realRoot 6 < (-4815 / 10000 : ℝ) := (realRoot_mem 6).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_6
  refine norm_cayley_sub_le (M := 1 / 200) (D := 123 / 100) (by norm_num)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by norm_num) (by nlinarith) (by norm_num)
theorem re_le_of_norm_le {z w : ℂ} {T : ℝ} (h : ‖z - w‖ ≤ T) :
    |z.re - w.re| ≤ T ∧ |z.im - w.im| ≤ T := by
  constructor
  · have hb := Complex.abs_re_le_norm (z - w)
    simp only [Complex.sub_re] at hb
    linarith
  · have hb := Complex.abs_im_le_norm (z - w)
    simp only [Complex.sub_im] at hb
    linarith
theorem zc2_comp : |zc2.re - vc2.re| ≤ 1 / 1000000 ∧ |zc2.im - vc2.im| ≤ 1 / 1000000 :=
  re_le_of_norm_le zc2_mem
theorem vc2_re_small : |vc2.re| ≤ 1 / 100000 := by
  rw [abs_le]
  unfold vc2
  constructor <;>
    (simp only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.I_re, Complex.I_im]; push_cast; norm_num)
theorem vc2_im_bounds : (8232 / 10000 : ℝ) ≤ vc2.im ∧ vc2.im ≤ 8233 / 10000 := by
  unfold vc2
  constructor <;>
    (simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
      Complex.I_re, Complex.I_im]; push_cast; norm_num)
theorem proj_R_bound :
    (cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im
      + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im)
      ≤ -(143 / 1000) := by
  obtain ⟨h3re, h3im⟩ := re_le_of_norm_le cayley3_near
  obtain ⟨h6re, h6im⟩ := re_le_of_norm_le cayley6_near
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  obtain ⟨⟨s1, s2⟩, ⟨t1, t2⟩⟩ := u_bounds_6
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h3re h3im h6re h6im q1 q2 hv1
  nlinarith [h3re.1, h3re.2, h3im.1, h3im.2, h6re.1, h6re.2, h6im.1, h6im.2,
    q1.1, q1.2, q2.1, q2.2, hv1.1, hv1.2, r1, r2, i1, i2, s1, s2, t1, t2, hv2, hv3]
theorem proj_R3_le_one :
    (cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im ≤ 1 := by
  obtain ⟨h3re, h3im⟩ := re_le_of_norm_le cayley3_near
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h3re h3im q1 q2 hv1
  nlinarith [h3re.1, h3re.2, h3im.1, h3im.2, q1.1, q1.2, q2.1, q2.2,
    hv1.1, hv1.2, r1, r2, i1, i2, hv2, hv3]
theorem proj_R6_le_one :
    (cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im ≤ 1 := by
  obtain ⟨h6re, h6im⟩ := re_le_of_norm_le cayley6_near
  obtain ⟨⟨s1, s2⟩, ⟨t1, t2⟩⟩ := u_bounds_6
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h6re h6im q1 q2 hv1
  nlinarith [h6re.1, h6re.2, h6im.1, h6im.2, q1.1, q1.2, q2.1, q2.2,
    hv1.1, hv1.2, s1, s2, t1, t2, hv2, hv3]
theorem one_sub_eps_re_le_norm {ζ q : ℂ} (hz : ‖ζ‖ = 1) {e : ℝ} (he : 0 ≤ e)
    (hle : e * (ζ.re * q.re + ζ.im * q.im) ≤ 1) :
    1 - e * (ζ.re * q.re + ζ.im * q.im) ≤ ‖ζ - ((e : ℝ) : ℂ) * q‖ := by
  have hns : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hz2 : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    rw [← hns]; simp only [Complex.normSq_apply]; ring
  have hq2 : Complex.normSq q = q.re ^ 2 + q.im ^ 2 := by
    simp only [Complex.normSq_apply]; ring
  have hcs : (ζ.re * q.re + ζ.im * q.im) ^ 2 ≤ Complex.normSq q := by
    rw [hq2]
    nlinarith [sq_nonneg (ζ.re * q.im - ζ.im * q.re), hz2]
  have hexp : Complex.normSq (ζ - ((e : ℝ) : ℂ) * q)
      = Complex.normSq ζ - 2 * e * (ζ.re * q.re + ζ.im * q.im)
        + e ^ 2 * Complex.normSq q := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply le_norm_of_le_normSq (by linarith)
  rw [hexp, hns]
  nlinarith [hcs, sq_nonneg e, mul_le_mul_of_nonneg_left hcs (sq_nonneg e)]
theorem eps_cast : (((ε : ℝ)) : ℂ) = ((ε : ℚ) : ℂ) := by push_cast; ring
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution :
    (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000))
      ≤ ‖physicalRoot 3 - zs‖ + ‖physicalRoot 6 - zs‖ := by
  have hRb := proj_R_bound
  have he : (0 : ℝ) ≤ (ε : ℝ) := eps_pos.le
  have heps1 : ((ε : ℝ)) ≤ 1 := by unfold ε s; norm_num
  have hle3 : (ε : ℝ) * ((cayley (realRoot 3)).re * zc2.re
      + (cayley (realRoot 3)).im * zc2.im) ≤ 1 := by
    nlinarith [proj_R3_le_one, he, heps1]
  have hle6 : (ε : ℝ) * ((cayley (realRoot 6)).re * zc2.re
      + (cayley (realRoot 6)).im * zc2.im) ≤ 1 := by
    nlinarith [proj_R6_le_one, he, heps1]
  have hb3 := one_sub_eps_re_le_norm (cayley_norm (realRoot 3)) he hle3
  have hb6 := one_sub_eps_re_le_norm (cayley_norm (realRoot 6)) he hle6
  have hp3 : physicalRoot 3 - zs
      = (ρ : ℂ) * (cayley (realRoot 3) - (((ε : ℝ)) : ℂ) * zc2) := by
    unfold physicalRoot zs
    rw [eps_cast]; ring
  have hp6 : physicalRoot 6 - zs
      = (ρ : ℂ) * (cayley (realRoot 6) - (((ε : ℝ)) : ℂ) * zc2) := by
    unfold physicalRoot zs
    rw [eps_cast]; ring
  have hmul : (ε : ℝ) * (143 / 1000)
      ≤ -((ε : ℝ) * (((cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im)
        + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im))) := by
    nlinarith [mul_nonneg he (by linarith [hRb] :
      (0 : ℝ) ≤ -(143 / 1000) - (((cayley (realRoot 3)).re * zc2.re
        + (cayley (realRoot 3)).im * zc2.im)
        + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im)))]
  have hsum : 2 + (ε : ℝ) * (143 / 1000)
      ≤ ‖cayley (realRoot 3) - (((ε : ℝ)) : ℂ) * zc2‖
        + ‖cayley (realRoot 6) - (((ε : ℝ)) : ℂ) * zc2‖ := by
    linarith [hb3, hb6, hmul]
  rw [hp3, hp6, norm_mul, norm_mul, Complex.norm_ratCast, abs_of_pos rho_pos]
  have hfin := mul_le_mul_of_nonneg_left hsum rho_pos.le
  linarith [hfin]
