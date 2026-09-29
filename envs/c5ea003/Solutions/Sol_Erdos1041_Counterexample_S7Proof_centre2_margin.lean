-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.centre2_margin
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:21:28.855431+00:00
-- url     : https://prove2.me/submissions/7ed33037-1359-4986-a908-09b40ca7a83e

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
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

theorem trig_medium (x : ℝ) (hlo : 3 / 7 ≤ x) (hhi : x ≤ 1 / 2) :
    1 / 3 ≤ Real.sin x ∧ Real.sin x ≤ 1 / 2 ∧
      7 / 8 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  have hx : 0 < x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx hx1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := pow_le_pow_left₀ hx.le hhi 2
  have h3 := pow_le_pow_left₀ hx.le hhi 3
  norm_num at h2 h3
  exact ⟨by linarith, (Real.sin_le hx.le).trans hhi,
    by linarith, Real.cos_le_one x⟩



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







theorem u4_re : (u 4).re = -Real.cos (Real.pi / 7) := by
  rw [u_re]
  have h : 2 * Real.pi * (4 : ℝ) / 7 = Real.pi + Real.pi / 7 := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add]

theorem u4_im : (u 4).im = -Real.sin (Real.pi / 7) := by
  rw [u_im]
  have h : 2 * Real.pi * (4 : ℝ) / 7 = Real.pi + Real.pi / 7 := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add]

theorem u5_re : (u 5).re = -Real.sin (Real.pi / 14) := by
  rw [u_re]
  have h : 2 * Real.pi * (5 : ℝ) / 7 = Real.pi + (Real.pi / 2 - Real.pi / 14) := by ring
  norm_num only
  rw [h]
  simp [Real.cos_add, Real.cos_sub]

theorem u5_im : (u 5).im = -Real.cos (Real.pi / 14) := by
  rw [u_im]
  have h : 2 * Real.pi * (5 : ℝ) / 7 = Real.pi + (Real.pi / 2 - Real.pi / 14) := by ring
  norm_num only
  rw [h]
  simp [Real.sin_add, Real.sin_sub]
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (j : ℕ) (hj : j = 4 ∨ j = 5) :
    2 ≤ -eta (u j) - |xi (u j)| := by
  rcases hj with rfl | rfl
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_medium (Real.pi / 7) (by linarith) (by linarith)
    have hx : 0 ≤ xi (u 4) := by
      unfold xi
      rw [u4_re, u4_im]
      linarith
    rw [abs_of_nonneg hx]
    unfold eta xi
    rw [u4_re, u4_im]
    linarith
  · obtain ⟨hp0, hp1⟩ := pi_coarse
    obtain ⟨hs0, hs1, hc0, hc1⟩ := trig_small (Real.pi / 14) (by linarith) (by linarith)
    have hx : xi (u 5) ≤ 0 := by
      unfold xi
      rw [u5_re, u5_im]
      linarith
    rw [abs_of_nonpos hx]
    unfold eta xi
    rw [u5_re, u5_im]
    linarith
