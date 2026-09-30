-- Prove2me | solution 1 for FedRemoval.ExactNewtonRemoval
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:54:49.819813+00:00
-- url     : https://prove2.me/submissions/a668bb4d-6eb4-47ad-875d-891235e9f874

import Mathlib
import Definitions.Def_FedRemoval_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Direct quadratic completion-of-squares proof for the removal surrogate.
Source: Jin et al., arXiv:2306.02216v3, Section III-B, PDF p. 5, equation (6);
supplementary Section C5, PDF p. 16, unnumbered displays.
-/

noncomputable section

open scoped BigOperators
open FedRemoval

set_option autoImplicit false

private lemma gram_positive {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n)) :
    (gram D s).IsPositive := by
  unfold gram
  exact (ContinuousLinearMap.isPositive_sum s (fun i _ ↦
    ContinuousLinearMap.isPositive_adjoint_comp_self (D.feature i))).smul_of_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private lemma hessian_unit {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (hμ : 0 < μ) : IsUnit (hessian D s μ) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (hessian D s μ)
    (c := ⟨μ, hμ.le⟩)
  · exact hμ
  · intro x
    change ‖x‖ ^ 2 * μ ≤ ‖inner ℝ (hessian D s μ x) x‖
    simp only [hessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    rw [Real.norm_eq_abs]
    exact le_trans (by nlinarith [(gram_positive D s).inner_nonneg_left x]) (le_abs_self _)

-- Gram positivity and coercivity helpers adapted from Minghui, accepted
-- SurrogateGap submission 34ae8eb3-e785-458b-9772-22674ade8db8.

theorem solution :
∀ (n d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ),
    s.Nonempty → 0 < μ →
    ∀ w, w - exactCorrection D s μ w = optimum D s μ := by
  intro n d k D s μ _hs hμ w
  have hi : inverseHessian D s μ (hessian D s μ w) = w := by
    have hh := congrArg (fun L : E d →L[ℝ] E d => L w)
      (Ring.inverse_mul_cancel (hessian D s μ) (hessian_unit D s μ hμ))
    simpa [inverseHessian, ContinuousLinearMap.mul_apply] using hh
  unfold exactCorrection ridgeGradient optimum
  rw [map_sub, hi]
  abel
