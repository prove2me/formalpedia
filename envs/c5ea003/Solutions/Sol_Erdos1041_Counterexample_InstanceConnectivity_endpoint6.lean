-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.endpoint6
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:17:32.629753+00:00
-- url     : https://prove2.me/submissions/e0154c30-1825-46f5-876a-05d0e470e549

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_bridge_radial
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_bridge_sector
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
theorem u6_eq : u6 = Complex.exp (((-2 * Real.pi / 7 : ℝ) : ℂ) * Complex.I) := by
  unfold u6; congr 1; push_cast; ring
theorem u6_norm : ‖u6‖ = 1 := by rw [u6_eq]; exact Complex.norm_exp_ofReal_mul_I _
theorem u6_re : u6.re = Real.cos (-2 * Real.pi / 7) := by
  rw [u6_eq]; exact Complex.exp_ofReal_mul_I_re _
theorem u6_im : u6.im = Real.sin (-2 * Real.pi / 7) := by
  rw [u6_eq]; exact Complex.exp_ofReal_mul_I_im _
theorem u6_pow7 : u6 ^ 7 = 1 := by
  have h : u6 ^ (7 : ℕ) = Complex.exp ((7 : ℕ) * (-2 * (Real.pi : ℂ) * Complex.I / 7)) :=
    (Complex.exp_nat_mul _ 7).symm
  rw [h]
  exact Complex.exp_eq_one_iff.mpr ⟨-1, by push_cast; ring⟩
theorem cos_enclosure {x lo hi : ℝ} (h0 : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi) (h1 : hi ≤ 1) :
    1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96) ≤ Real.cos x ∧
      Real.cos x ≤ 1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96) := by
  have hx0 : 0 ≤ x := le_trans h0 hlo
  have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.cos_bound hx1
  have hax : |x| = x := abs_of_nonneg hx0
  rw [hax, abs_le] at hb
  have h2 : x ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hx0 hhi 2
  have h2' : lo ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h0 hlo 2
  have h4 : x ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hx0 hhi 4
  exact ⟨by nlinarith [hb.1], by nlinarith [hb.2]⟩
theorem sin_enclosure {x lo hi : ℝ} (h0 : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi) (h1 : hi ≤ 1) :
    lo - hi ^ 3 / 6 - hi ^ 4 * (5 / 96) ≤ Real.sin x ∧
      Real.sin x ≤ hi - lo ^ 3 / 6 + hi ^ 4 * (5 / 96) := by
  have hx0 : 0 ≤ x := le_trans h0 hlo
  have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound hx1
  have hax : |x| = x := abs_of_nonneg hx0
  rw [hax, abs_le] at hb
  have h3 : x ^ 3 ≤ hi ^ 3 := pow_le_pow_left₀ hx0 hhi 3
  have h3' : lo ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ h0 hlo 3
  have h4 : x ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hx0 hhi 4
  exact ⟨by nlinarith [hb.1], by nlinarith [hb.2]⟩
theorem two_pi_div7_lo : (3141592 / 3500000 : ℝ) ≤ 2 * Real.pi / 7 := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith
theorem two_pi_div7_hi : 2 * Real.pi / 7 ≤ 3141593 / 3500000 := by
  have h := Real.pi_lt_d6
  norm_num at h ⊢
  linarith
theorem cos_neg2pi7 : Real.cos (-2 * Real.pi / 7) = Real.cos (2 * Real.pi / 7) := by
  have h : -2 * Real.pi / 7 = -(2 * Real.pi / 7) := by ring
  rw [h, Real.cos_neg]
theorem sin_neg2pi7 : Real.sin (-2 * Real.pi / 7) = -Real.sin (2 * Real.pi / 7) := by
  have h : -2 * Real.pi / 7 = -(2 * Real.pi / 7) := by ring
  rw [h, Real.sin_neg]
theorem anchor6 : ‖m6 / 8 - u6‖ ≤ 1 / 10 := by
  obtain ⟨hc1, hc2⟩ := cos_enclosure (lo := (3141592 / 3500000 : ℝ)) (hi := 3141593 / 3500000)
    (by norm_num) two_pi_div7_lo two_pi_div7_hi (by norm_num)
  obtain ⟨hs1, hs2⟩ := sin_enclosure (lo := (3141592 / 3500000 : ℝ)) (hi := 3141593 / 3500000)
    (by norm_num) two_pi_div7_lo two_pi_div7_hi (by norm_num)
  refine norm_le_of_normSq_le (by norm_num) ?_
  have hmr : (m6 / 8).re = 498791841486986824420 / (8 * 10 ^ 20) := by
    norm_num [m6, Complex.div_re, Complex.normSq_apply]
  have hmi : (m6 / 8).im = -625465185974423846967 / (8 * 10 ^ 20) := by
    norm_num [m6, Complex.div_im, Complex.normSq_apply]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, u6_re, u6_im, cos_neg2pi7,
    sin_neg2pi7, hmr, hmi]
  norm_num at hc1 hc2 hs1 hs2 ⊢
  nlinarith [hc1, hc2, hs1, hs2]
theorem norm_m6_div8 : ‖m6 / 8‖ ≤ 101 / 100 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [m6, Complex.normSq_apply, Complex.div_re, Complex.div_im])
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (b₆ : ℂ) (hr₆ : f.IsRoot b₆)
    (hnear₆ : ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10) :
    JoinedIn (Omega f) (scale m6) b₆ :=
  (bridge_sector b₆ m6 u6 anchor6 norm_m6_div8 u6_norm u6_pow7 hr₆ hnear₆).trans
    (bridge_radial b₆ hr₆)
