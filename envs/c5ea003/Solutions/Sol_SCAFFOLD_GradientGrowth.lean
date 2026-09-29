-- Prove2me | solution 1 for SCAFFOLD.GradientGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-24T06:20:49.857683+00:00
-- url     : https://prove2.me/submissions/ce3f70f1-cf8a-4626-ac11-61d00f48daf8

import Definitions.Def_SCAFFOLD_Model
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

/-!
Karimireddy et al., SCAFFOLD, arXiv:1910.06378v4, Appendix B.1, PDF p. 14,
equations (7)--(9), in the setup of Section 5. The proof first derives the
smooth convex gradient-gap inequality, then sums it and uses first-order
optimality of the average objective. No individual common minimizer is assumed.
The analytic helpers follow the already checked local FedAvg/SmoothConvex module,
and are included here so this upload needs only the public SCAFFOLD model.
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open Set SCAFFOLD

namespace SCAFFOLDGradientGrowthProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem gradient_line_deriv {f : E → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (x y : E) (t : ℝ) :
    HasDerivAt (f ∘ AffineMap.lineMap x y)
      ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ t := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap

private theorem smooth_descent {f : E → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  let a := ⟪gradient f x, y - x⟫_ℝ
  let b := L / 2 * ‖y - x‖ ^ 2
  let B : ℝ → ℝ := fun t ↦ f x + t * a + t ^ 2 * b
  have hBder (t : ℝ) : HasDerivAt B (a + 2 * t * b) t := by
    convert (((hasDerivAt_id t).mul_const a).const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const b) using 1
    simp
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ ≤ a + 2 * t * b := by
    have hn : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      simp [AffineMap.lineMap_apply_module', norm_smul, abs_of_nonneg ht.1]
    have hgrad := mul_le_mul_of_nonneg_right (hs (AffineMap.lineMap x y t) x)
      (norm_nonneg (y - x))
    have hi := real_inner_le_norm (gradient f (AffineMap.lineMap x y t) - gradient f x)
      (y - x)
    rw [hn] at hgrad
    rw [inner_sub_left] at hi
    dsimp [a, b]
    nlinarith
  have hfinal := image_le_of_deriv_right_le_deriv_boundary
    (f := f ∘ AffineMap.lineMap x y)
    (f' := fun t ↦ ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ)
    (a := 0) (b := 1)
    (by exact (continuous_iff_continuousAt.mpr fun t ↦
      (gradient_line_deriv hf x y t).continuousAt).continuousOn)
    (fun t _ ↦ (gradient_line_deriv hf x y t).hasDerivWithinAt)
    (B := B) (B' := fun t ↦ a + 2 * t * b)
    (by simp [B])
    (by exact (continuous_iff_continuousAt.mpr fun t ↦ (hBder t).continuousAt).continuousOn)
    (fun t _ ↦ (hBder t).hasDerivWithinAt) hbound
    (x := 1) (by simp)
  simpa [B, a, b] using hfinal

private theorem smooth_convex_gap {f : E → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y) (hL : 0 < L)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    ‖gradient f x - gradient f y‖ ^ 2 ≤
      2 * L * (f x - f y - ⟪gradient f y, x - y⟫_ℝ) := by
  let v := gradient f x - gradient f y
  let z := x - L⁻¹ • v
  have hzx : z - x = -(L⁻¹ • v) := by dsimp [z]; abel
  have hzy : z - y = (x - y) - L⁻¹ • v := by dsimp [z]; abel
  have hdes := smooth_descent hf hs x z
  have hlo := hc y z
  rw [hzx, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)] at hdes
  rw [hzy, inner_sub_right, inner_smul_right] at hlo
  have hv : ⟪gradient f x, v⟫_ℝ - ⟪gradient f y, v⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq v
  have heq : -(L⁻¹ * ⟪gradient f x, v⟫_ℝ) + L / 2 * (L⁻¹ * ‖v‖) ^ 2 +
      L⁻¹ * ⟪gradient f y, v⟫_ℝ = -(‖v‖ ^ 2 / (2 * L)) := by
    field_simp
    nlinarith [hv]
  have hgap : ‖v‖ ^ 2 / (2 * L) ≤ f x - f y - ⟪gradient f y, x - y⟫_ℝ := by
    linarith
  have hh := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hgap
  simpa only [mul_comm] using hh

private theorem objective_hasGradient {d N : ℕ} (P : Problem d N) (x : Space d) :
    HasGradientAt (objective P.f) ((N : ℝ)⁻¹ • ∑ i, gradient (P.f i) x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [objective, map_smul, map_sum] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (P.hasGradient i x).hasFDerivAt)).const_mul (N : ℝ)⁻¹

end SCAFFOLDGradientGrowthProof

theorem solution :
  ∀ (d N : ℕ) (P : Problem d N) (xstar : Space d),
    Convexity P 0 → IsMinimizer P xstar → ∀ x,
      (N : ℝ)⁻¹ * ∑ i, ‖gradient (P.f i) x - gradient (P.f i) xstar‖ ^ 2 ≤
        2 * P.β * (objective P.f x - objective P.f xstar) := by
  intro d N P xstar hc hm x
  have hmin : IsLocalMin (objective P.f) xstar := Filter.Eventually.of_forall hm
  have hzero : gradient (objective P.f) xstar = 0 := by
    rw [gradient, hmin.fderiv_eq_zero, map_zero]
  have hsum : (N : ℝ)⁻¹ • ∑ i, gradient (P.f i) xstar = 0 := by
    rw [← (SCAFFOLDGradientGrowthProof.objective_hasGradient P xstar).gradient, hzero]
  have hi (i : Fin N) :
      ‖gradient (P.f i) x - gradient (P.f i) xstar‖ ^ 2 ≤
        2 * P.β * (P.f i x - P.f i xstar -
          ⟪gradient (P.f i) xstar, x - xstar⟫_ℝ) := by
    apply SCAFFOLDGradientGrowthProof.smooth_convex_gap (P.hasGradient i)
      (fun z w ↦ ?_) P.smoothness_pos (P.smooth i)
    simpa only [zero_div, zero_mul, add_zero] using hc.2 i z w
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hi i)
    (inv_nonneg.mpr (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
  have hlin : (N : ℝ)⁻¹ * ∑ i, ⟪gradient (P.f i) xstar, x - xstar⟫_ℝ = 0 := by
    rw [← sum_inner, ← real_inner_smul_left, hsum, inner_zero_left]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at hh
  have hz := congrArg (fun z : ℝ ↦ 2 * P.β * z) hlin
  unfold objective
  nlinarith only [hh, hz]
