-- Prove2me | solution 1 for ConvexOptimization.convexOn_iff_gradient_inequality
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:14:41.810903+00:00
-- url     : https://prove2.me/submissions/d5989919-da3c-4757-8043-f0b9ac755cd5

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ Ω, HasGradientAt f (f' x) x) :
    ConvexOn ℝ Ω f ↔ ∀ x ∈ Ω, ∀ y ∈ Ω, f x + ⟪f' x, y - x⟫ ≤ f y := by
  constructor
  · -- Convexity ⇒ the first-order (supporting hyperplane) inequality.
    -- Restrict `f` to the line through `x` and `y` and use the 1-D fact that the
    -- derivative at the left endpoint is at most the slope of the chord.
    intro hconv x hx y hy
    set L : ℝ → EuclideanSpace ℝ (Fin n) := fun t => t • (y - x) + x with hL
    have hL0 : L 0 = x := by simp [hL]
    have hL1 : L 1 = y := by simp [hL]
    -- `L` as an affine map, so that `ConvexOn.comp_affineMap` applies.
    set A : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
      { toFun := L
        linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
        map_vadd' := by intro p v; simp [hL, add_smul]; module } with hA
    have hAcoe : ⇑A = L := rfl
    have hφconv : ConvexOn ℝ (A ⁻¹' Ω) (f ∘ A) := hconv.comp_affineMap A
    have h0 : (0 : ℝ) ∈ A ⁻¹' Ω := by simpa [hAcoe, hL0] using hx
    have h1 : (1 : ℝ) ∈ A ⁻¹' Ω := by simpa [hAcoe, hL1] using hy
    -- The chain rule along the line.
    have hline : HasDerivAt L (y - x) 0 := by
      simpa [hL] using (((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x)
    have hcomp : HasDerivAt (f ∘ A) (⟪f' x, y - x⟫) 0 := by
      have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (f' x)) (L 0) := by
        rw [hL0]; exact (hf x hx).hasFDerivAt
      simpa [hAcoe] using hfd.comp_hasDerivAt 0 hline
    have hslope := hφconv.le_slope_of_hasDerivAt h0 h1 zero_lt_one hcomp
    rw [slope_def_field] at hslope
    simp only [Function.comp_apply, hAcoe, hL0, hL1, sub_zero, div_one] at hslope
    linarith
  · -- The first-order inequality ⇒ convexity: average the two tangent bounds at
    -- the convex combination point.
    intro hgrad
    refine ⟨hΩc, fun p hp q hq a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    set z : EuclideanSpace ℝ (Fin n) := a • p + b • q with hz
    have hzΩ : z ∈ Ω := hΩc hp hq ha hb hab
    have h1 := hgrad z hzΩ p hp
    have h2 := hgrad z hzΩ q hq
    have hcomb : a • (p - z) + b • (q - z) = 0 := by
      have hexp : a • (p - z) + b • (q - z) = (a • p + b • q) - (a + b) • z := by module
      rw [hexp, hab, one_smul, hz, sub_self]
    have hinner : a * ⟪f' z, p - z⟫ + b * ⟪f' z, q - z⟫ = 0 := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb,
        inner_zero_right]
    have e1 : a * (f z + ⟪f' z, p - z⟫) ≤ a * f p := mul_le_mul_of_nonneg_left h1 ha
    have e2 : b * (f z + ⟪f' z, q - z⟫) ≤ b * f q := mul_le_mul_of_nonneg_left h2 hb
    rw [mul_add] at e1 e2
    have hsum : a * f z + b * f z = f z := by rw [← add_mul, hab, one_mul]
    linarith [e1, e2, hsum, hinner]
