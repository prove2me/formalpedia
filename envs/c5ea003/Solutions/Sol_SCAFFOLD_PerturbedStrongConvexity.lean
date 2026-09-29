-- Prove2me | solution 1 for SCAFFOLD.PerturbedStrongConvexity
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-24T06:21:11.133981+00:00
-- url     : https://prove2.me/submissions/dd28a805-94a0-49a5-b9e2-f995028eda2b

import Definitions.Def_SCAFFOLD_Model
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
Karimireddy et al., SCAFFOLD, arXiv:1910.06378v4, Appendix C,
PDF p. 17, Lemma 5 (unnumbered displays), used in Section 5.
The smooth-descent helper specializes the mean-value comparison theorem; its proof
reuses the local, already checked argument in `Definitions/FedAvg/SmoothConvex.lean`.
Only the public SCAFFOLD model and Mathlib are imported.
-/

noncomputable section

open scoped InnerProductSpace
open Set SCAFFOLD

private theorem gradient_line_deriv {d : ℕ} {f : Space d → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (x y : Space d) (t : ℝ) :
    HasDerivAt (f ∘ AffineMap.lineMap x y)
      ⟪gradient f (AffineMap.lineMap x y t), y - x⟫_ℝ t := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap

private theorem smooth_descent {d : ℕ} {f : Space d → ℝ} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : Space d) :
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

theorem solution :
  ∀ (d N : ℕ) (P : Problem d N) (μ : ℝ), Convexity P μ →
    ∀ (i : Fin N) (x y z : Space d),
      P.f i z - P.f i y + μ / 4 * ‖y - z‖ ^ 2 - P.β * ‖z - x‖ ^ 2 ≤
        inner ℝ (gradient (P.f i) x) (z - y) := by
  intro d N P μ hconv i x y z
  have hdes := smooth_descent (P.hasGradient i) (P.smooth i) x z
  have hxy := hconv.2 i x y
  have hxz := hconv.2 i x z
  have habsorb : μ * ‖z - x‖ ^ 2 ≤ P.β * ‖z - x‖ ^ 2 := by
    linarith
  have htriangle : ‖y - z‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖z - x‖ ^ 2 := by
    have hnorm : ‖y - z‖ ≤ ‖y - x‖ + ‖z - x‖ := by
      simpa only [sub_add_sub_cancel, norm_sub_rev x z] using norm_add_le (y - x) (x - z)
    nlinarith [norm_nonneg (y - z), norm_nonneg (y - x), norm_nonneg (z - x),
      sq_nonneg (‖y - x‖ - ‖z - x‖)]
  have hscaled := mul_le_mul_of_nonneg_left htriangle hconv.1
  have hinner : inner ℝ (gradient (P.f i) x) (z - y) =
      inner ℝ (gradient (P.f i) x) (z - x) -
        inner ℝ (gradient (P.f i) x) (y - x) := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [hinner]
  nlinarith
