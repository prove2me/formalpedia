-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.endpoint3
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:17:32.112929+00:00
-- url     : https://prove2.me/submissions/b175a8cd-1416-449a-8644-0e2713ac5d69

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
theorem u3_eq : u3 = Complex.exp (((6 * Real.pi / 7 : ℝ) : ℂ) * Complex.I) := by
  unfold u3; congr 1; push_cast; ring
theorem u3_norm : ‖u3‖ = 1 := by rw [u3_eq]; exact Complex.norm_exp_ofReal_mul_I _
theorem u3_re : u3.re = Real.cos (6 * Real.pi / 7) := by
  rw [u3_eq]; exact Complex.exp_ofReal_mul_I_re _
theorem u3_im : u3.im = Real.sin (6 * Real.pi / 7) := by
  rw [u3_eq]; exact Complex.exp_ofReal_mul_I_im _
theorem u3_pow7 : u3 ^ 7 = 1 := by
  have h : u3 ^ (7 : ℕ) = Complex.exp ((7 : ℕ) * (6 * (Real.pi : ℂ) * Complex.I / 7)) :=
    (Complex.exp_nat_mul _ 7).symm
  rw [h]
  exact Complex.exp_eq_one_iff.mpr ⟨3, by push_cast; ring⟩
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
theorem pi_div7_lo : (3141592 / 7000000 : ℝ) ≤ Real.pi / 7 := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith
theorem pi_div7_hi : Real.pi / 7 ≤ 3141593 / 7000000 := by
  have h := Real.pi_lt_d6
  norm_num at h ⊢
  linarith
theorem cos_6pi7 : Real.cos (6 * Real.pi / 7) = -Real.cos (Real.pi / 7) := by
  have h : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  rw [h, Real.cos_pi_sub]
theorem sin_6pi7 : Real.sin (6 * Real.pi / 7) = Real.sin (Real.pi / 7) := by
  have h : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  rw [h, Real.sin_pi_sub]
theorem anchor3 : ‖m3 / 8 - u3‖ ≤ 1 / 10 := by
  obtain ⟨hc1, hc2⟩ := cos_enclosure (lo := (3141592 / 7000000 : ℝ)) (hi := 3141593 / 7000000)
    (by norm_num) pi_div7_lo pi_div7_hi (by norm_num)
  obtain ⟨hs1, hs2⟩ := sin_enclosure (lo := (3141592 / 7000000 : ℝ)) (hi := 3141593 / 7000000)
    (by norm_num) pi_div7_lo pi_div7_hi (by norm_num)
  refine norm_le_of_normSq_le (by norm_num) ?_
  have hmr : (m3 / 8).re = -720775094321935300989 / (8 * 10 ^ 20) := by
    norm_num [m3, Complex.div_re, Complex.normSq_apply]
  have hmi : (m3 / 8).im = 347106991294046496381 / (8 * 10 ^ 20) := by
    norm_num [m3, Complex.div_im, Complex.normSq_apply]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, u3_re, u3_im, cos_6pi7, sin_6pi7,
    hmr, hmi]
  norm_num at hc1 hc2 hs1 hs2 ⊢
  nlinarith [hc1, hc2, hs1, hs2]
theorem norm_m3_div8 : ‖m3 / 8‖ ≤ 101 / 100 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [m3, Complex.normSq_apply, Complex.div_re, Complex.div_im])
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (b₃ : ℂ) (hr₃ : f.IsRoot b₃)
    (hnear₃ : ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10) :
    JoinedIn (Omega f) (scale m3) b₃ :=
  (bridge_sector b₃ m3 u3 anchor3 norm_m3_div8 u3_norm u3_pow7 hr₃ hnear₃).trans
    (bridge_radial b₃ hr₃)
