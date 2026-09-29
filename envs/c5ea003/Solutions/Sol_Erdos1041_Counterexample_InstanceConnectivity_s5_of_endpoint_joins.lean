-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.s5_of_endpoint_joins
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:07:14.372434+00:00
-- url     : https://prove2.me/submissions/f7b77dbd-3059-4585-97a1-38596fd34d4f

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
theorem Q_re (w : ℂ) : (Q.eval w).re = qRe w.re w.im := by
  norm_num [Q, P, G, E, a, b, c, A, B, Cconst, t, s, qRe, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.conj_ofNat] <;> ring
theorem Q_im (w : ℂ) : (Q.eval w).im = qIm w.re w.im := by
  norm_num [Q, P, G, E, a, b, c, A, B, Cconst, t, s, qIm, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.conj_ofNat] <;> ring
theorem Hlo_eq_Hxy (w : ℂ) : Hlo w = Hxy w.re w.im := by
  simp only [Hlo, Hxy, Complex.normSq_apply, Q_re, Q_im]
  norm_num [ε, s] <;> ring
theorem Hlo_affine (w₀ w₁ : ℂ) (τ : ℝ) :
    Hlo (affine w₀ w₁ τ) =
      Hxy (w₀.re + τ * (w₁.re - w₀.re)) (w₀.im + τ * (w₁.im - w₀.im)) := by
  rw [Hlo_eq_Hxy]
  simp [affine, Complex.mul_re, Complex.mul_im]
theorem P3a_certificate (τ : ℝ) :
    (P3a_denominator : ℝ) * (Hlo (affine wq x3 τ) - (7 / 2000000)) = P3a_rhs τ := by
  rw [Hlo_affine]
  norm_num [P3a_denominator, P3a_rhs, Hxy, qRe, qIm, wq, x3] <;> ring
theorem P3a_rhs_nonneg (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ P3a_rhs τ := by
  have h₀ : 0 ≤ τ := hτ.1
  have h₁ : 0 ≤ 1 - τ := sub_nonneg.mpr hτ.2
  dsimp [P3a_rhs]
  positivity
theorem P3a_lower (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (7 / 2000000) ≤ Hlo (affine wq x3 τ) := by
  have h : 0 ≤ (P3a_denominator : ℝ) * (Hlo (affine wq x3 τ) - (7 / 2000000)) := by
    rw [P3a_certificate]
    exact P3a_rhs_nonneg τ hτ
  norm_num [P3a_denominator] at h
  nlinarith only [h]
theorem P3a_positive (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 < Hlo (affine wq x3 τ) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7 / 2000000)) (P3a_lower τ hτ)
theorem P3b_certificate (τ : ℝ) :
    (P3b_denominator : ℝ) * (Hlo (affine x3 m3 τ) - (640000)) = P3b_rhs τ := by
  rw [Hlo_affine]
  norm_num [P3b_denominator, P3b_rhs, Hxy, qRe, qIm, x3, m3] <;> ring
theorem P3b_rhs_nonneg (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ P3b_rhs τ := by
  have h₀ : 0 ≤ τ := hτ.1
  have h₁ : 0 ≤ 1 - τ := sub_nonneg.mpr hτ.2
  dsimp [P3b_rhs]
  positivity
theorem P3b_lower (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (640000) ≤ Hlo (affine x3 m3 τ) := by
  have h : 0 ≤ (P3b_denominator : ℝ) * (Hlo (affine x3 m3 τ) - (640000)) := by
    rw [P3b_certificate]
    exact P3b_rhs_nonneg τ hτ
  norm_num [P3b_denominator] at h
  nlinarith only [h]
theorem P3b_positive (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 < Hlo (affine x3 m3 τ) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < (640000)) (P3b_lower τ hτ)
theorem P6a_certificate (τ : ℝ) :
    (P6a_denominator : ℝ) * (Hlo (affine wq x6 τ) - (7 / 2000000)) = P6a_rhs τ := by
  rw [Hlo_affine]
  norm_num [P6a_denominator, P6a_rhs, Hxy, qRe, qIm, wq, x6] <;> ring
theorem P6a_rhs_nonneg (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ P6a_rhs τ := by
  have h₀ : 0 ≤ τ := hτ.1
  have h₁ : 0 ≤ 1 - τ := sub_nonneg.mpr hτ.2
  dsimp [P6a_rhs]
  positivity
theorem P6a_lower (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (7 / 2000000) ≤ Hlo (affine wq x6 τ) := by
  have h : 0 ≤ (P6a_denominator : ℝ) * (Hlo (affine wq x6 τ) - (7 / 2000000)) := by
    rw [P6a_certificate]
    exact P6a_rhs_nonneg τ hτ
  norm_num [P6a_denominator] at h
  nlinarith only [h]
theorem P6a_positive (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 < Hlo (affine wq x6 τ) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7 / 2000000)) (P6a_lower τ hτ)
theorem P6b_certificate (τ : ℝ) :
    (P6b_denominator : ℝ) * (Hlo (affine x6 m6 τ) - (139000)) = P6b_rhs τ := by
  rw [Hlo_affine]
  norm_num [P6b_denominator, P6b_rhs, Hxy, qRe, qIm, x6, m6] <;> ring
theorem P6b_rhs_nonneg (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ P6b_rhs τ := by
  have h₀ : 0 ≤ τ := hτ.1
  have h₁ : 0 ≤ 1 - τ := sub_nonneg.mpr hτ.2
  dsimp [P6b_rhs]
  positivity
theorem P6b_lower (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (139000) ≤ Hlo (affine x6 m6 τ) := by
  have h : 0 ≤ (P6b_denominator : ℝ) * (Hlo (affine x6 m6 τ) - (139000)) := by
    rw [P6b_certificate]
    exact P6b_rhs_nonneg τ hτ
  norm_num [P6b_denominator] at h
  nlinarith only [h]
theorem P6b_positive (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    0 < Hlo (affine x6 m6 τ) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < (139000)) (P6b_lower τ hτ)
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
/-- Both entire rational-centre polylines, without any S4 or S5 admission. -/
theorem scaled_polylines :
    JoinedIn (Omega f) (scale wq) (scale m3) ∧
      JoinedIn (Omega f) (scale wq) (scale m6) := by
  constructor
  · exact (joinedIn_of_Hlo_affine_pos wq x3 P3a_positive).trans
      (joinedIn_of_Hlo_affine_pos x3 m3 P3b_positive)
  · exact (joinedIn_of_Hlo_affine_pos wq x6 P6a_positive).trans
      (joinedIn_of_Hlo_affine_pos x6 m6 P6b_positive)
/-- The relative connected-component bridge, using the confirmed Mathlib API. -/
theorem mem_component_of_joined {x y : ℂ} (h : JoinedIn (Omega f) x y) :
    y ∈ connectedComponentIn (Omega f) x := by
  rcases h with ⟨γ, hγ⟩
  have hc := (isConnected_range γ.continuous).isPreconnected
  apply hc.subset_connectedComponentIn
    (show x ∈ Set.range γ from ⟨0, γ.source⟩)
    (show Set.range γ ⊆ Omega f from ?_)
    (show y ∈ Set.range γ from ⟨1, γ.target⟩)
  rintro _ ⟨τ, rfl⟩
  exact hγ τ
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (zs b₃ b₆ : ℂ)
    (hstart : JoinedIn (Omega f) zs (scale wq))
    (hend₃ : JoinedIn (Omega f) (scale m3) b₃)
    (hend₆ : JoinedIn (Omega f) (scale m6) b₆) :
    b₃ ∈ connectedComponentIn (Omega f) zs ∧
      b₆ ∈ connectedComponentIn (Omega f) zs := by
  exact ⟨mem_component_of_joined ((hstart.trans scaled_polylines.1).trans hend₃),
    mem_component_of_joined ((hstart.trans scaled_polylines.2).trans hend₆)⟩
