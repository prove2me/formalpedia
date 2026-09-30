-- Prove2me | solution 1 for FedRemoval.SurrogateGap
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T22:03:25.129828+00:00
-- url     : https://prove2.me/submissions/34ae8eb3-e785-458b-9772-22674ade8db8

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

private lemma quadratic_gap {d : ℕ} (H : E d →L[ℝ] E d) (g u v : E d)
    (hp : H.IsPositive) (hu : H u = g) :
    ((1 / 2 : ℝ) * inner ℝ v (H v) - inner ℝ g v) -
        ((1 / 2 : ℝ) * inner ℝ u (H u) - inner ℝ g u) =
      (1 / 2 : ℝ) * inner ℝ (v - u) (H (v - u)) := by
  have hsym : inner ℝ u (H v) = inner ℝ v (H u) := by
    rw [← hp.inner_left_eq_inner_right u v, real_inner_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [← hu, hsym, real_inner_comm (H u) v, real_inner_comm (H u) u]
  ring

theorem solution :
    ∀ (n q d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k) (μ : ℝ),
      s.Nonempty → 0 < q → 0 < μ →
      ∀ w v,
        solverGap D s P μ w v = (1 / 2 : ℝ) *
          inner ℝ (v - surrogateOptimum D s P μ w)
            (hessian P Finset.univ μ (v - surrogateOptimum D s P μ w)) ∧
        μ / 2 * ‖v - surrogateOptimum D s P μ w‖ ^ 2 ≤ solverGap D s P μ w v := by
  intro n q d k D s P μ _hs _hq hμ w v
  have hg := gram_positive P Finset.univ
  have hp : (hessian P Finset.univ μ).IsPositive :=
    hg.add (ContinuousLinearMap.isPositive_id.smul_of_nonneg hμ.le)
  have hu : hessian P Finset.univ μ (surrogateOptimum D s P μ w) =
      ridgeGradient D s μ w := by
    have h := congrArg (fun A : E d →L[ℝ] E d ↦ A (ridgeGradient D s μ w))
      (Ring.mul_inverse_cancel (hessian P Finset.univ μ)
        (hessian_unit P Finset.univ μ hμ))
    simpa [surrogateOptimum, inverseHessian, ContinuousLinearMap.mul_apply] using h
  have hgap : solverGap D s P μ w v = (1 / 2 : ℝ) *
      inner ℝ (v - surrogateOptimum D s P μ w)
        (hessian P Finset.univ μ (v - surrogateOptimum D s P μ w)) := by
    exact quadratic_gap (hessian P Finset.univ μ) (ridgeGradient D s μ w)
      (surrogateOptimum D s P μ w) v hp hu
  refine ⟨hgap, ?_⟩
  rw [hgap]
  simp only [hessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith [hg.inner_nonneg_right (v - surrogateOptimum D s P μ w)]
