-- Prove2me | solution 1 for FedRemoval.InversePerturbation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:54:50.479434+00:00
-- url     : https://prove2.me/submissions/86d86147-2b2b-4f90-9698-42daeb3673b2

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
∀ (n q d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k) (μ : ℝ),
    s.Nonempty → 0 < q → 0 < μ →
    inverseHessian P Finset.univ μ - inverseHessian D s μ =
      (inverseHessian P Finset.univ μ).comp
        ((gram D s - gram P Finset.univ).comp (inverseHessian D s μ)) ∧
    ‖inverseHessian P Finset.univ μ - inverseHessian D s μ‖ ≤
      ‖inverseHessian P Finset.univ μ‖ * ‖gram D s - gram P Finset.univ‖ *
        ‖inverseHessian D s μ‖ := by
  intro n q d k D s P μ _hs _hq hμ
  have hd := hessian_unit D s μ hμ
  have hp := hessian_unit P Finset.univ μ hμ
  have hdiff : hessian D s μ - hessian P Finset.univ μ = gram D s - gram P Finset.univ := by
    unfold hessian
    abel
  have hraw := Ring.inverse_sub_inverse (a := hessian P Finset.univ μ)
    (b := hessian D s μ) (iff_of_true hp hd)
  rw [hdiff] at hraw
  have hid : inverseHessian P Finset.univ μ - inverseHessian D s μ =
      (inverseHessian P Finset.univ μ).comp
        ((gram D s - gram P Finset.univ).comp (inverseHessian D s μ)) := by
    simpa only [inverseHessian, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hraw
  refine ⟨hid, ?_⟩
  rw [hid]
  calc
    _ ≤ ‖inverseHessian P Finset.univ μ‖ * ‖(gram D s - gram P Finset.univ).comp (inverseHessian D s μ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖inverseHessian P Finset.univ μ‖ * (‖gram D s - gram P Finset.univ‖ * ‖inverseHessian D s μ‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring
