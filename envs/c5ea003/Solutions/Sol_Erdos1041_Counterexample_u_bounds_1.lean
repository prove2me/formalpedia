-- Prove2me | solution 1 for Erdos1041.Counterexample.u_bounds_1
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:30:26.494768+00:00
-- url     : https://prove2.me/submissions/fe9dc455-9177-4938-8a16-48dd6b8a5f85

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_cos_two_pi_div_seven_bounds
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

namespace Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem two_pi_div_seven_lb : (8975977 / 10 ^ 7 : ℝ) < 2 * Real.pi / 7 := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith
theorem two_pi_div_seven_pos : 0 < 2 * Real.pi / 7 := by
  have := two_pi_div_seven_lb; linarith
theorem two_pi_div_seven_lt_pi : 2 * Real.pi / 7 < Real.pi := by
  have := Real.pi_pos; linarith
/-- `sin(2π/7) ∈ (0.7817, 0.7820)`. -/
theorem sin_two_pi_div_seven_bounds :
    (7817 / 10000 : ℝ) < Real.sin (2 * Real.pi / 7) ∧
      Real.sin (2 * Real.pi / 7) < (7820 / 10000 : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cos_two_pi_div_seven_bounds
  have hsq : Real.sin (2 * Real.pi / 7) ^ 2 = 1 - Real.cos (2 * Real.pi / 7) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * Real.pi / 7)
    linarith
  have hpos : 0 < Real.sin (2 * Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi two_pi_div_seven_pos two_pi_div_seven_lt_pi
  constructor <;> nlinarith [hsq, hpos, hc1, hc2]
theorem u_one_eq : u 1
    = ((Real.cos (2 * Real.pi / 7) : ℝ) : ℂ)
      + ((Real.sin (2 * Real.pi / 7) : ℝ) : ℂ) * Complex.I := by
  unfold u
  have h : (2 * (Real.pi : ℂ) * ((1 : ℕ) : ℂ) * Complex.I / 7)
      = (((2 * Real.pi / 7 : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
theorem u_one_re : (u 1).re = Real.cos (2 * Real.pi / 7) := by
  rw [u_one_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
theorem u_one_im : (u 1).im = Real.sin (2 * Real.pi / 7) := by
  rw [u_one_eq]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    ((6234 / 10000 : ℝ) ≤ (u 1).re ∧ (u 1).re ≤ 6236 / 10000) ∧
      ((7817 / 10000 : ℝ) ≤ (u 1).im ∧ (u 1).im ≤ 7820 / 10000) := by
  rw [u_one_re, u_one_im]
  obtain ⟨c1, c2⟩ := cos_two_pi_div_seven_bounds
  obtain ⟨s1, s2⟩ := sin_two_pi_div_seven_bounds
  exact ⟨⟨c1.le, c2.le⟩, ⟨s1.le, s2.le⟩⟩
