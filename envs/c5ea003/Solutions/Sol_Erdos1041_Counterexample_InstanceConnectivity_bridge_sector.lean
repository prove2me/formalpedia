-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.bridge_sector
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:08:58.945977+00:00
-- url     : https://prove2.me/submissions/7347e443-7314-4e0c-861c-e3238c112c4c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_Hlo_sector_pos
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_root_norm_le
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
theorem rho_ne_zeroC : ((ρ : ℚ) : ℂ) ≠ 0 := by
  have h : (ρ : ℚ) ≠ 0 := by norm_num [ρ, s]
  exact_mod_cast h
theorem F_eval_of_root {bj : ℂ} (hroot : f.IsRoot bj) : F.eval (bj / (ρ : ℂ)) = 0 := by
  have hρ0 : ((ρ:ℚ):ℂ) ≠ 0 := rho_ne_zeroC
  have h := f_eval_scale (bj / (ρ : ℂ))
  have hb : (ρ:ℂ) * (bj / (ρ:ℂ)) = bj := by field_simp
  rw [hb, show f.eval bj = 0 from hroot] at h
  rcases mul_eq_zero.mp h.symm with h3 | h3
  · exact absurd h3 (pow_ne_zero 7 hρ0)
  · exact h3
theorem zeta_norm_le {bj : ℂ} (hroot : f.IsRoot bj) : ‖bj / (ρ : ℂ)‖ ≤ 101 / 100 :=
  root_norm_le _ (F_eval_of_root hroot)
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (bj mj uj : ℂ)
    (hmu : ‖mj / 8 - uj‖ ≤ 1 / 10) (hmn : ‖mj / 8‖ ≤ 101 / 100)
    (hu : ‖uj‖ = 1) (hu7 : uj ^ 7 = 1)
    (hroot : f.IsRoot bj)
    (hnear : ‖bj - (ρ : ℂ) * uj‖ < (ρ : ℝ) / 10) :
    JoinedIn (Omega f) (scale mj) (8 * (ε : ℂ) * bj) := by
  have hρ0 : ((ρ:ℚ):ℂ) ≠ 0 := rho_ne_zeroC
  have hrp : (0:ℝ) < (ρ:ℝ) := rho_pos
  have hzn : ‖bj / (ρ:ℂ)‖ ≤ 101 / 100 := zeta_norm_le hroot
  have hzu : ‖bj / (ρ:ℂ) - uj‖ ≤ 1 / 10 := by
    have he : bj / (ρ:ℂ) - uj = (bj - (ρ:ℂ) * uj) / (ρ:ℂ) := by field_simp
    rw [he, norm_div, Complex.norm_ratCast, abs_of_pos hrp, div_le_iff₀ hrp]
    linarith [hnear]
  have hpath : JoinedIn (Omega f) (scale mj) (scale (8 * (bj / (ρ:ℂ)))) := by
    apply joinedIn_of_Hlo_affine_pos
    intro τ hτ
    have hx : affine mj (8 * (bj / (ρ:ℂ))) τ
        = 8 * (((1 - τ : ℝ) : ℂ) * (mj / 8) + ((τ : ℝ) : ℂ) * (bj / (ρ:ℂ))) := by
      simp only [affine]; push_cast; ring
    rw [hx]
    have n1 : ‖(((1 - τ : ℝ)) : ℂ)‖ = 1 - τ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2])]
    have n2 : ‖((τ : ℝ) : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    refine Hlo_sector_pos _ uj hu hu7 ?_ ?_
    · have hsp : ((1 - τ : ℝ) : ℂ) * (mj / 8) + ((τ : ℝ) : ℂ) * (bj / (ρ:ℂ)) - uj
          = ((1 - τ : ℝ) : ℂ) * (mj / 8 - uj) + ((τ : ℝ) : ℂ) * (bj / (ρ:ℂ) - uj) := by
        push_cast; ring
      rw [hsp]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, n1, n2]
      nlinarith [hmu, hzu, hτ.1, hτ.2, norm_nonneg (mj / 8 - uj), norm_nonneg (bj / (ρ:ℂ) - uj)]
    · refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, n1, n2]
      nlinarith [hmn, hzn, hτ.1, hτ.2, norm_nonneg (mj / 8), norm_nonneg (bj / (ρ:ℂ))]
  have hend : scale (8 * (bj / (ρ:ℂ))) = 8 * (ε : ℂ) * bj := by
    simp only [scale]; field_simp
  rwa [hend] at hpath
