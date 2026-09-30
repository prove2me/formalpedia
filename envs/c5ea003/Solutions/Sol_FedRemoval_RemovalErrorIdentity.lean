-- Prove2me | solution 1 for FedRemoval.RemovalErrorIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T22:03:24.610357+00:00
-- url     : https://prove2.me/submissions/b6ea8976-a712-4438-a128-ab758938c8ba

import Definitions.Def_FedRemoval_Model
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Direct proof of the corrected signed removal decomposition.
Source: Jin et al., arXiv:2306.02216v3, Section III-C, PDF pp. 5--6, Theorem 2;
supplementary Section C5, PDF p. 16, unnumbered error-decomposition displays.
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

theorem solution :
    ∀ (n q d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k) (μ : ℝ),
      s.Nonempty → 0 < q → 0 < μ →
      ∀ w v r,
        w - v - r =
          inverseHessian P Finset.univ μ
            ((gram P Finset.univ - gram D s) (w - optimum D s μ)) +
          (surrogateOptimum D s P μ w - v) + (optimum D s μ - r) := by
  intro n q d k D s P μ _hs _hq hμ w v r
  have huS : hessian D s μ (optimum D s μ) = rhs D s := by
    have h := congrArg (fun A : E d →L[ℝ] E d ↦ A (rhs D s))
      (Ring.mul_inverse_cancel (hessian D s μ) (hessian_unit D s μ hμ))
    simpa [optimum, inverseHessian, ContinuousLinearMap.mul_apply] using h
  have hcancelP (x : E d) :
      inverseHessian P Finset.univ μ (hessian P Finset.univ μ x) = x := by
    have h := congrArg (fun A : E d →L[ℝ] E d ↦ A x)
      (Ring.inverse_mul_cancel (hessian P Finset.univ μ)
        (hessian_unit P Finset.univ μ hμ))
    simpa [inverseHessian, ContinuousLinearMap.mul_apply] using h
  have hgrad : ridgeGradient D s μ w = hessian D s μ (w - optimum D s μ) := by
    simp only [ridgeGradient, map_sub, huS]
  have hdiff (x : E d) :
      (gram P Finset.univ - gram D s) x =
        hessian P Finset.univ μ x - hessian D s μ x := by
    simp only [hessian, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    abel
  have hsum :
      (gram P Finset.univ - gram D s) (w - optimum D s μ) + ridgeGradient D s μ w =
        hessian P Finset.univ μ (w - optimum D s μ) := by
    rw [hdiff, hgrad]
    abel
  have hkey :
      inverseHessian P Finset.univ μ
          ((gram P Finset.univ - gram D s) (w - optimum D s μ)) +
        surrogateOptimum D s P μ w = w - optimum D s μ := by
    rw [surrogateOptimum, ← map_add, hsum, hcancelP]
  rw [sub_eq_add_neg (surrogateOptimum D s P μ w) v, ← add_assoc,
    hkey]
  abel
