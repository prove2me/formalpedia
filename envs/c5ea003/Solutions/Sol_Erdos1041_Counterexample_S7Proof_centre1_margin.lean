-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.centre1_margin
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:21:28.20325+00:00
-- url     : https://prove2.me/submissions/6456b075-a439-4522-b49d-f561c69f4cbb

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_abs_xi_le
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

noncomputable section

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000









/-- Only coarse Taylor brackets are required; no algebraic minimal polynomial
or floating-point approximation to a trigonometric value is used. -/
theorem trig_small (x : ℝ) (hlo : 3 / 14 ≤ x) (hhi : x ≤ 1 / 4) :
    1 / 5 ≤ Real.sin x ∧ Real.sin x ≤ 1 / 4 ∧
      31 / 32 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  have hx : 0 < x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx hx1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := pow_le_pow_left₀ hx.le hhi 2
  have h3 := pow_le_pow_left₀ hx.le hhi 3
  norm_num at h2 h3
  exact ⟨by linarith, (Real.sin_le hx.le).trans hhi,
    by linarith, Real.cos_le_one x⟩



theorem trig_large (x : ℝ) (hlo : 6 / 7 ≤ x) (hhi : x ≤ 1) :
    1 / 2 ≤ Real.sin x ∧ 1 / 2 ≤ Real.cos x := by
  have hx : 0 < x := by linarith
  have hs := Real.sin_gt_sub_cube hx hhi
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 : x ^ 2 ≤ 1 := by nlinarith
  have h3 : x ^ 3 ≤ 1 := by nlinarith
  exact ⟨by linarith, by linarith⟩

theorem pi_coarse : (3 : ℝ) < Real.pi ∧ Real.pi < 7 / 2 := by
  exact ⟨Real.pi_gt_three, by linarith [Real.pi_lt_d2]⟩

theorem u_form (j : ℕ) :
    u j = Complex.exp ((((2 * Real.pi * (j : ℝ) / 7 : ℝ) : ℂ)) * Complex.I) := by
  unfold u
  congr 1
  push_cast
  <;> ring

theorem u_re (j : ℕ) : (u j).re = Real.cos (2 * Real.pi * (j : ℝ) / 7) := by
  rw [u_form]
  exact Complex.exp_ofReal_mul_I_re _

theorem u_im (j : ℕ) : (u j).im = Real.sin (2 * Real.pi * (j : ℝ) / 7) := by
  rw [u_form]
  exact Complex.exp_ofReal_mul_I_im _

theorem norm_u (j : ℕ) : ‖u j‖ = 1 := by
  rw [u_form]
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem u2_re : (u 2).re = -Real.sin (Real.pi / 14) := by
  rw [u_re]
  have h : 2 * Real.pi * (2 : ℝ) / 7 = Real.pi / 2 + Real.pi / 14 := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add]

theorem u2_im : (u 2).im = Real.cos (Real.pi / 14) := by
  rw [u_im]
  have h : 2 * Real.pi * (2 : ℝ) / 7 = Real.pi / 2 + Real.pi / 14 := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add]
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (j : ℕ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    3 / 2 ≤ eta (u j) - (1 / 4 : ℝ) * |xi (u j)| := by
  rcases hj with rfl | rfl | rfl
  · norm_num [eta, xi, u]
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs, hc⟩ := trig_large (2 * Real.pi / 7) (by linarith) (by linarith)
    have he : 9 / 2 ≤ eta (u 1) := by
      unfold eta
      rw [u_re, u_im]
      norm_num only [mul_one]
      linarith
    have hx := abs_xi_le (u 1)
    rw [norm_u] at hx
    linarith
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_small (Real.pi / 14) (by linarith) (by linarith)
    have he : 123 / 32 ≤ eta (u 2) := by
      unfold eta
      rw [u2_re, u2_im]
      linarith
    have hx := abs_xi_le (u 2)
    rw [norm_u] at hx
    linarith
