-- Prove2me | solution 1 for FedRemoval.RidgeStructure
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:07:20.311743+00:00
-- url     : https://prove2.me/submissions/bd1f4bb4-2626-40ed-9951-8c20b6817a9c

import Mathlib
import Definitions.Def_FedRemoval_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Ridge loss structure from positivity, differentiation, and quadratic completion.
The gram_positive, hessian_unit, and quadratic_gap helpers are adapted from
Minghui's accepted FedRemoval.SurrogateGap submission
34ae8eb3-e785-458b-9772-22674ade8db8 on prove2.me.
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

-- Positivity, coercivity and quadratic-gap helpers adapted from Minghui,
-- accepted SurrogateGap submission 34ae8eb3-e785-458b-9772-22674ade8db8.

private theorem ridge_gradient {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (w : E d) : HasGradientAt (loss D s μ) (ridgeGradient D s μ w) w := by
  have hi (i : Fin n) := ((((D.feature i).hasFDerivAt (x := w)).add_const (D.offset i)).sub_const (D.target i)).norm_sq
  have hsum := HasFDerivAt.sum (u := s) (fun i _ => hi i)
  have hderiv := (hsum.const_mul ((2 * (s.card : ℝ))⁻¹)).add
    (((hasFDerivAt_id w).norm_sq).const_mul (μ / 2))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hderiv using 1 <;> try rfl
  · ext z
    simp [loss, predict, Finset.sum_apply]
  · ext v
    simp [ridgeGradient, hessian, gram, rhs, InnerProductSpace.toDual_apply_apply,
      sum_inner, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
      inner_add_left, inner_sub_left]
    ring_nf
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring

private theorem quadratic_gradient {d : ℕ} (H : E d →L[ℝ] E d)
    (hp : H.IsPositive) (b w : E d) :
    HasGradientAt (fun x => (1 / 2 : ℝ) * inner ℝ x (H x) - inner ℝ b x) (H w - b) w := by
  have h1 := ((hasFDerivAt_id w).inner ℝ (H.hasFDerivAt (x := w))).const_mul (1 / 2 : ℝ)
  have h2 := (hasFDerivAt_const b w).inner ℝ (hasFDerivAt_id w)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h1.sub h2 using 1 <;> try rfl
  ext v
  simp [InnerProductSpace.toDual_apply_apply, fderivInnerCLM_apply, inner_sub_left]
  rw [← hp.inner_left_eq_inner_right w v, real_inner_comm v (H w)]
  ring

private theorem ridge_lower {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (w : E d) : μ * ‖w‖ ^ 2 ≤ inner ℝ w (hessian D s μ w) := by
  simp only [hessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith [(gram_positive D s).inner_nonneg_right w]

private theorem inverse_norm_bound {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (hμ : 0 < μ) : ‖inverseHessian D s μ‖ ≤ μ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro y
  let x := inverseHessian D s μ y
  have hh : hessian D s μ x = y := by
    have h := congrArg (fun L : E d →L[ℝ] E d => L y)
      (Ring.mul_inverse_cancel (hessian D s μ) (hessian_unit D s μ hμ))
    simpa [x, inverseHessian, ContinuousLinearMap.mul_apply] using h
  have hlow := ridge_lower D s μ x
  rw [hh] at hlow
  have hupper := real_inner_le_norm x y
  have hnorm : μ * ‖x‖ ≤ ‖y‖ := by
    by_cases hx : ‖x‖ = 0
    · simp [hx]
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      nlinarith
  have hb : ‖x‖ ≤ ‖y‖ / μ := (le_div_iff₀ hμ).mpr (by simpa [mul_comm] using hnorm)
  simpa [x, div_eq_mul_inv, mul_comm] using hb

private theorem loss_gap {n d k : ℕ} (D : Data n d k) (s : Finset (Fin n))
    (μ : ℝ) (hμ : 0 < μ) (w : E d) :
    loss D s μ w = loss D s μ (optimum D s μ) + (1 / 2 : ℝ) *
      inner ℝ (w - optimum D s μ) (hessian D s μ (w - optimum D s μ)) := by
  let H := hessian D s μ
  let b := rhs D s
  let u := optimum D s μ
  let Q : E d → ℝ := fun x => (1 / 2 : ℝ) * inner ℝ x (H x) - inner ℝ b x
  have hp : H.IsPositive := (gram_positive D s).add
    (ContinuousLinearMap.isPositive_id.smul_of_nonneg hμ.le)
  have hdiff (x : E d) : HasFDerivAt (fun z => loss D s μ z - Q z) (0 : E d →L[ℝ] ℝ) x := by
    have hf := hasGradientAt_iff_hasFDerivAt.mp (ridge_gradient D s μ x)
    have hq := hasGradientAt_iff_hasFDerivAt.mp (quadratic_gradient H hp b x)
    convert hf.sub hq using 1 <;> try rfl
    all_goals simp [ridgeGradient, H, b, Q]
  have hconstant := is_const_of_fderiv_eq_zero (fun x => (hdiff x).differentiableAt)
    (fun x => (hdiff x).fderiv) w u
  have hu : H u = b := by
    have h := congrArg (fun L : E d →L[ℝ] E d => L b)
      (Ring.mul_inverse_cancel (hessian D s μ) (hessian_unit D s μ hμ))
    simpa [H, u, optimum, inverseHessian, ContinuousLinearMap.mul_apply] using h
  have hg := quadratic_gap H b u w hp hu
  change Q w - Q u = _ at hg
  change loss D s μ w - Q w = loss D s μ u - Q u at hconstant
  change loss D s μ w = loss D s μ u + (1 / 2 : ℝ) * inner ℝ (w - u) (H (w - u))
  linarith

theorem solution :
∀ (n d k : ℕ) (D : Data n d k) (s : Finset (Fin n)) (μ : ℝ),
    s.Nonempty → 0 < μ →
    IsUnit (hessian D s μ) ∧
    ‖inverseHessian D s μ‖ ≤ μ⁻¹ ∧
    (∀ w, HasGradientAt (loss D s μ) (ridgeGradient D s μ w) w) ∧
    (∀ w, μ * ‖w‖ ^ 2 ≤ inner ℝ w (hessian D s μ w)) ∧
    (∀ w, loss D s μ w = loss D s μ (optimum D s μ) +
      (1 / 2 : ℝ) * inner ℝ (w - optimum D s μ)
        (hessian D s μ (w - optimum D s μ))) ∧
    (∀ w, (∀ z, loss D s μ w ≤ loss D s μ z) ↔ w = optimum D s μ) := by
  intro n d k D s μ _hs hμ
  refine ⟨hessian_unit D s μ hμ, inverse_norm_bound D s μ hμ,
    ridge_gradient D s μ, ridge_lower D s μ, loss_gap D s μ hμ, ?_⟩
  intro w
  constructor
  · intro hmin
    have hm := hmin (optimum D s μ)
    have hg := loss_gap D s μ hμ w
    have hl := ridge_lower D s μ (w - optimum D s μ)
    have hsq : μ * ‖w - optimum D s μ‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (mul_nonneg hμ.le (sq_nonneg _))
    have hn : ‖w - optimum D s μ‖ = 0 :=
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq).resolve_left (ne_of_gt hμ))
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · rintro rfl z
    have hg := loss_gap D s μ hμ z
    have hl := ridge_lower D s μ (z - optimum D s μ)
    nlinarith [mul_nonneg hμ.le (sq_nonneg ‖z - optimum D s μ‖)]
