-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.joined_zs_wq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:08:59.467113+00:00
-- url     : https://prove2.me/submissions/24648637-c3dc-443c-be8e-b478676694eb

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_Hlo_disc_pos
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_delta_small
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
theorem rho_pos : 0 < (ρ : ℝ) := by
  norm_num [ρ, s]
theorem epsilon_pos : 0 < (ε : ℝ) := by
  norm_num [ε, s]
theorem f_eval_scale (z : ℂ) :
    f.eval ((ρ : ℂ) * z) = (ρ : ℂ) ^ 7 * F.eval z := by
  simp only [f, F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring
theorem F_eval_scaled (w : ℂ) :
    F.eval ((ε : ℂ) * w) = -1 + (ε : ℂ) ^ 7 * Q.eval w := by
  norm_num [F, Q, P, G, E, a, b, c, ε, s, A, B, Cconst, t] <;> ring
theorem f_eval_scaled (w : ℂ) :
    f.eval (scale w) = (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
  change f.eval ((ρ : ℂ) * (ε : ℂ) * w) = _
  rw [mul_assoc, f_eval_scale, F_eval_scaled]
theorem normSq_perturbation (r : ℝ) (z : ℂ) :
    Complex.normSq (-1 + (r : ℂ) * z) =
      1 - 2 * r * z.re + r ^ 2 * Complex.normSq z := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring
/-- The nonnegative contraction allowance, checked as a rational inequality. -/
theorem contraction_budget :
    0 ≤ 1 - (ρ : ℝ) ^ 14 - 14 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 8 := by
  norm_num [ρ, ε, s]
theorem energy_identity (w : ℂ) :
    1 - ‖f.eval (scale w)‖ ^ 2 =
      (1 - (ρ : ℝ) ^ 14 - 14 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 8) +
        2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hlo w := by
  have hc : (ε : ℂ) ^ 7 = (((ε : ℝ) ^ 7 : ℝ) : ℂ) := by
    norm_cast
  rw [f_eval_scaled, norm_mul, norm_pow, Complex.norm_ratCast,
    abs_of_pos rho_pos, mul_pow, Complex.sq_norm, hc, normSq_perturbation]
  dsimp [Hlo]
  ring
theorem Hlo_pos_mem (w : ℂ) (hw : 0 < Hlo w) : scale w ∈ Omega f := by
  have hp : 0 < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 := by
    have := rho_pos
    have := epsilon_pos
    positivity
  have he := energy_identity w
  have hb := contraction_budget
  have hprod : 0 < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hlo w := mul_pos hp hw
  have hdef : 0 < 1 - ‖f.eval (scale w)‖ ^ 2 := by linarith
  change ‖f.eval (scale w)‖ < 1
  have hn := norm_nonneg (f.eval (scale w))
  nlinarith only [hdef, hn]
/-- Turn a uniformly positive affine segment into a path in the physical plane. -/
theorem joinedIn_of_Hlo_affine_pos (w₀ w₁ : ℂ)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < Hlo (affine w₀ w₁ τ)) :
    JoinedIn (Omega f) (scale w₀) (scale w₁) := by
  apply JoinedIn.ofLine (f := fun τ : ℝ => scale (affine w₀ w₁ τ))
  · exact (show Continuous (fun τ : ℝ => scale (affine w₀ w₁ τ)) from by
      dsimp [scale, affine]
      fun_prop).continuousOn
  · norm_num [scale, affine] <;> ring
  · norm_num [scale, affine] <;> ring
  · rintro _ ⟨τ, hτ, rfl⟩
    exact Hlo_pos_mem _ (h τ hτ)
theorem Q_eval (w : ℂ) :
    Q.eval w = w ^ 7 + p6 * w ^ 6 + p5 * w ^ 5 + p4 * w ^ 4 + p3 * w ^ 3 + p2 * w ^ 2 + p1 * w := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num [a, b, c, A, B, Cconst, t, s, p1, p2, p3, p4, p5, p6, Complex.conj_ofNat]
  ring
theorem norm_le_of_normSq_le {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : Complex.normSq z ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem rho_ne_zeroC : ((ρ : ℚ) : ℂ) ≠ 0 := by
  have h : (ρ : ℚ) ≠ 0 := by norm_num [ρ, s]
  exact_mod_cast h
theorem eps_ne_zeroC : ((ε : ℚ) : ℂ) ≠ 0 := by
  have h : (ε : ℚ) ≠ 0 := by norm_num [ε, s]
  exact_mod_cast h
theorem Q_hasDerivAt (w : ℂ) : HasDerivAt (fun z : ℂ => Q.eval z) (Qd w) w := by
  have hfun : (fun z : ℂ => Q.eval z)
      = fun z : ℂ => z ^ 7 + p6 * z ^ 6 + p5 * z ^ 5 + p4 * z ^ 4 + p3 * z ^ 3 + p2 * z ^ 2
        + p1 * z := by
    funext z; exact Q_eval z
  rw [hfun]
  have e7 := hasDerivAt_pow 7 w
  have e6 := (hasDerivAt_pow 6 w).const_mul p6
  have e5 := (hasDerivAt_pow 5 w).const_mul p5
  have e4 := (hasDerivAt_pow 4 w).const_mul p4
  have e3 := (hasDerivAt_pow 3 w).const_mul p3
  have e2 := (hasDerivAt_pow 2 w).const_mul p2
  have e1 := (hasDerivAt_pow 1 w).const_mul p1
  have hall := ((((((e7.add e6).add e5).add e4).add e3).add e2).add e1)
  have hsimp : (fun z : ℂ => z ^ 7 + p6 * z ^ 6 + p5 * z ^ 5 + p4 * z ^ 4 + p3 * z ^ 3
      + p2 * z ^ 2 + p1 * z)
      = fun z : ℂ => z ^ 7 + p6 * z ^ 6 + p5 * z ^ 5 + p4 * z ^ 4 + p3 * z ^ 3 + p2 * z ^ 2
        + p1 * z ^ 1 := by
    funext z; ring
  rw [hsimp]
  convert hall using 1
  simp only [Qd]
  push_cast
  ring
theorem Qd_zero (zs : ℂ) (hcrit : (Polynomial.derivative f).IsRoot zs) :
    Qd (zs / ((ρ : ℂ) * (ε : ℂ))) = 0 := by
  have hcne : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zeroC eps_ne_zeroC
  have hcw : (ρ : ℂ) * (ε : ℂ) * (zs / ((ρ : ℂ) * (ε : ℂ))) = zs := by
    field_simp
    rw [mul_comm ((ρ : ℂ) * (ε : ℂ)) zs, mul_div_assoc, div_self hcne, mul_one]
  have hlin : HasDerivAt (fun w : ℂ => (ρ : ℂ) * (ε : ℂ) * w) ((ρ : ℂ) * (ε : ℂ))
      (zs / ((ρ : ℂ) * (ε : ℂ))) := by
    simpa using (hasDerivAt_id (zs / ((ρ : ℂ) * (ε : ℂ)))).const_mul ((ρ : ℂ) * (ε : ℂ))
  have h1 : HasDerivAt (fun w : ℂ => f.eval ((ρ : ℂ) * (ε : ℂ) * w))
      ((Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * (zs / ((ρ : ℂ) * (ε : ℂ))))
        * ((ρ : ℂ) * (ε : ℂ))) (zs / ((ρ : ℂ) * (ε : ℂ))) :=
    (Polynomial.hasDerivAt f _).comp _ hlin
  rw [hcw, show (Polynomial.derivative f).eval zs = 0 from hcrit, zero_mul] at h1
  have h2 : HasDerivAt (fun w : ℂ => (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w))
      ((ρ : ℂ) ^ 7 * ((ε : ℂ) ^ 7 * Qd (zs / ((ρ : ℂ) * (ε : ℂ)))))
      (zs / ((ρ : ℂ) * (ε : ℂ))) := by
    have hb := ((Q_hasDerivAt (zs / ((ρ : ℂ) * (ε : ℂ)))).const_mul ((ε : ℂ) ^ 7)).const_add (-1)
    simpa using hb.const_mul ((ρ : ℂ) ^ 7)
  have hfun : (fun w : ℂ => f.eval ((ρ : ℂ) * (ε : ℂ) * w))
      = fun w : ℂ => (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
    funext w
    exact f_eval_scaled w
  rw [hfun] at h1
  have heq := h1.unique h2
  rcases mul_eq_zero.mp heq.symm with h | h
  · exact absurd h (pow_ne_zero 7 rho_ne_zeroC)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero 7 eps_ne_zeroC)
    · exact h'
theorem wbar_near_wq :
    ‖(((823247 / 1000000 : ℚ)) : ℂ) * Complex.I - wq‖ ≤ 1 / 10 ^ 6 :=
  norm_le_of_normSq_le (by norm_num)
    (by norm_num [wq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im])
theorem w_near_wq (zs : ℂ)
    (hloc : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ‖zs / ((ρ : ℂ) * (ε : ℂ)) - wq‖ ≤ 1 / 500 := by
  have hrp : (0:ℝ) < (ρ:ℝ) := rho_pos
  have hep : (0:ℝ) < (ε:ℝ) := epsilon_pos
  have hcne : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zeroC eps_ne_zeroC
  have hcn : ‖((ρ : ℂ) * (ε : ℂ))‖ = (ρ:ℝ) * (ε:ℝ) := by
    rw [norm_mul, Complex.norm_ratCast, Complex.norm_ratCast, abs_of_pos hrp, abs_of_pos hep]
  have hsplit : zs / ((ρ : ℂ) * (ε : ℂ)) - wq
      = (zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I)
          / ((ρ : ℂ) * (ε : ℂ))
        + ((((823247 / 1000000 : ℚ)) : ℂ) * Complex.I - wq) := by
    have h : ((ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I)
        / ((ρ : ℂ) * (ε : ℂ)) = (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I := by
      rw [show ((ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I)
          = ((((823247 / 1000000 : ℚ)) : ℂ) * Complex.I) * ((ρ : ℂ) * (ε : ℂ)) from by ring,
        mul_div_assoc, div_self hcne, mul_one]
    rw [sub_div, h]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_div, hcn]
  have h1 : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I‖
      / ((ρ:ℝ) * (ε:ℝ)) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hloc]
  linarith [wbar_near_wq]
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (zs : ℂ)
    (hcrit : (Polynomial.derivative f).IsRoot zs)
    (hloc : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    JoinedIn (Omega f) zs (scale wq) := by
  have hcne : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zeroC eps_ne_zeroC
  have hsw : scale (zs / ((ρ : ℂ) * (ε : ℂ))) = zs := by
    simp only [scale]
    field_simp
    rw [mul_comm ((ρ : ℂ) * (ε : ℂ)) zs, mul_div_assoc, div_self hcne, mul_one]
  rw [← hsw]
  have hsmall := delta_small _ (Qd_zero zs hcrit) (w_near_wq zs hloc)
  apply joinedIn_of_Hlo_affine_pos
  intro τ hτ
  have haff : affine (zs / ((ρ : ℂ) * (ε : ℂ))) wq τ
      = wq + (((1 - τ : ℝ)) : ℂ) * (zs / ((ρ : ℂ) * (ε : ℂ)) - wq) := by
    simp only [affine]; push_cast; ring
  rw [haff]
  apply Hlo_disc_pos
  rw [norm_mul]
  have n1 : ‖(((1 - τ : ℝ)) : ℂ)‖ = 1 - τ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2])]
  rw [n1]
  nlinarith [hsmall, hτ.1, hτ.2, norm_nonneg (zs / ((ρ : ℂ) * (ε : ℂ)) - wq)]
