-- Prove2me | solution 1 for ConvexOptimization.kkt_sufficient_for_convex
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T15:32:38.610387+00:00
-- url     : https://prove2.me/submissions/564037f2-2ee8-4e9c-bd1f-729f74b40299

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality
import Definitions.Def_ConvexOptimization_IsKKTPoint

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

private theorem convex_gradient_lower_bound {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf' : ∀ x, HasGradientAt f (f' x) x)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + ⟪f' x, y - x⟫ ≤ f y := by
  let g : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x y
  have hmaps : Set.MapsTo g (Set.Icc 0 1) Set.univ := fun _ _ => Set.mem_univ _
  have hgconv : ConvexOn ℝ (Set.Icc 0 1) (f ∘ g) :=
    (hf.comp_affineMap g).subset hmaps (convex_Icc 0 1)
  have hgderiv : HasDerivAt (f ∘ g) ⟪f' x, y - x⟫ 0 := by
    have hcomp := (hf' x).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
      (by simp)
    simpa [g] using hcomp
  have hslope : ⟪f' x, y - x⟫ ≤ slope (f ∘ g) 0 1 :=
    hgconv.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
      (Set.right_mem_Icc.2 zero_le_one) zero_lt_one hgderiv
  have hsecant : ⟪f' x, y - x⟫ ≤ f y - f x := by
    simpa [slope_def_field, g] using hslope
  linarith

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf₀' : ∀ x, HasGradientAt f₀ (f₀' x) x)
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hfc' : ∀ i x, HasGradientAt (fc i) (fc' i x) x)
    (xs : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (nu : Fin p → ℝ)
    (hkkt : IsKKTPoint fc a b f₀' fc' xs lam nu) :
    xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs := by
  rcases hkkt with ⟨hxs_ineq, hxs_eq, hlam, hcomp, hstat⟩
  refine ⟨⟨hxs_ineq, hxs_eq⟩, ?_⟩
  intro y hy
  have hobj := convex_gradient_lower_bound f₀ hf₀ f₀' hf₀' xs y
  have hconstraint (i : Fin mm) : ⟪fc' i xs, y - xs⟫ ≤ -fc i xs := by
    have hi := convex_gradient_lower_bound (fc i) (hfc i) (fc' i) (hfc' i) xs y
    linarith [hy.1 i]
  have hweighted (i : Fin mm) : lam i * ⟪fc' i xs, y - xs⟫ ≤ 0 := by
    calc
      lam i * ⟪fc' i xs, y - xs⟫ ≤ lam i * (-fc i xs) :=
        mul_le_mul_of_nonneg_left (hconstraint i) (hlam i)
      _ = 0 := by simp [hcomp i]
  have hsum_nonpos : (∑ i, lam i * ⟪fc' i xs, y - xs⟫) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hweighted i
  have heqdir (j : Fin p) : ⟪a j, y - xs⟫ = 0 := by
    rw [inner_sub_right, hy.2 j, hxs_eq j, sub_self]
  have hnusum : (∑ j, nu j * ⟪a j, y - xs⟫) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [heqdir j]
  have hstat_inner :
      ⟪f₀' xs, y - xs⟫ + ∑ i, lam i * ⟪fc' i xs, y - xs⟫ +
          ∑ j, nu j * ⟪a j, y - xs⟫ = 0 := by
    calc
      _ = ⟪f₀' xs + ∑ i, lam i • fc' i xs + ∑ j, nu j • a j, y - xs⟫ := by
        simp [inner_add_left, sum_inner, real_inner_smul_left]
      _ = 0 := by rw [hstat]; simp
  have hobjdir : 0 ≤ ⟪f₀' xs, y - xs⟫ := by
    linarith
  exact (le_add_of_nonneg_right hobjdir).trans hobj
