-- Prove2me | solution 1 for ConvexOptimization.lagrangian_saddle_iff_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T15:08:07.483406+00:00
-- url     : https://prove2.me/submissions/30d60b45-4407-453e-b757-b40b3b561649

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (nu : Fin p → ℝ) :
    ((∀ (lam' : Fin mm → ℝ), (∀ i, 0 ≤ lam' i) → ∀ nu' : Fin p → ℝ,
        lagrangian f₀ fc a b xs lam' nu' ≤ lagrangian f₀ fc a b xs lam nu) ∧
     (∀ x, lagrangian f₀ fc a b xs lam nu ≤ lagrangian f₀ fc a b x lam nu)) ↔
    (xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs ∧
     dualFunction f₀ fc a b lam nu = (f₀ xs : EReal)) := by
  have lagrangian_le_objective
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ feasibleSet fc a b)
      (mu : Fin mm → ℝ) (hmu : ∀ i, 0 ≤ mu i) (eta : Fin p → ℝ) :
      lagrangian f₀ fc a b x mu eta ≤ f₀ x := by
    have hineq : (∑ i, mu i * fc i x) ≤ 0 := by
      exact Finset.sum_nonpos fun i _ =>
        mul_nonpos_of_nonneg_of_nonpos (hmu i) (hx.1 i)
    have heq : (∑ j, eta j * (⟪a j, x⟫ - b j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx.2 j]
      ring
    simp only [lagrangian]
    rw [heq]
    linarith
  constructor
  · rintro ⟨hdualSide, hprimalSide⟩
    have hineq : ∀ i, fc i xs ≤ 0 := by
      intro i
      let lam' : Fin mm → ℝ := fun k => lam k + if k = i then 1 else 0
      have hlam' : ∀ k, 0 ≤ lam' k := by
        intro k
        exact add_nonneg (hlam k) (by split <;> norm_num)
      have h := hdualSide lam' hlam' nu
      simp only [lagrangian, lam', add_mul, Finset.sum_add_distrib] at h
      simp at h
      linarith
    have heq : ∀ j, ⟪a j, xs⟫ = b j := by
      intro j
      let nuPlus : Fin p → ℝ := fun k => nu k + if k = j then 1 else 0
      let nuMinus : Fin p → ℝ := fun k => nu k - if k = j then 1 else 0
      have hp := hdualSide lam hlam nuPlus
      have hm := hdualSide lam hlam nuMinus
      simp only [lagrangian, nuPlus, add_mul, Finset.sum_add_distrib] at hp
      simp only [lagrangian, nuMinus, sub_mul, Finset.sum_sub_distrib] at hm
      simp at hp hm
      linarith
    have hfeas : xs ∈ feasibleSet fc a b := ⟨hineq, heq⟩
    have hobj_le_L : f₀ xs ≤ lagrangian f₀ fc a b xs lam nu := by
      simpa [lagrangian] using
        (hdualSide (fun _ => 0) (by simp) (fun _ => 0))
    have hL_eq : lagrangian f₀ fc a b xs lam nu = f₀ xs :=
      le_antisymm (lagrangian_le_objective xs hfeas lam hlam nu) hobj_le_L
    have hmin : IsMinOn f₀ (feasibleSet fc a b) xs := by
      intro x hx
      calc
        f₀ xs = lagrangian f₀ fc a b xs lam nu := hL_eq.symm
        _ ≤ lagrangian f₀ fc a b x lam nu := hprimalSide x
        _ ≤ f₀ x := lagrangian_le_objective x hx lam hlam nu
    have hdualL : dualFunction f₀ fc a b lam nu =
        (lagrangian f₀ fc a b xs lam nu : EReal) := by
      apply le_antisymm
      · exact iInf_le _ xs
      · exact le_iInf fun x => EReal.coe_le_coe_iff.mpr (hprimalSide x)
    have hstrong : dualFunction f₀ fc a b lam nu = (f₀ xs : EReal) := by
      rw [hdualL, hL_eq]
    exact ⟨hfeas, hmin, hstrong⟩
  · rintro ⟨hfeas, _hmin, hstrong⟩
    have hobj_le_L : ∀ x, f₀ xs ≤ lagrangian f₀ fc a b x lam nu := by
      intro x
      apply EReal.coe_le_coe_iff.mp
      rw [← hstrong]
      exact iInf_le _ x
    have hL_eq : lagrangian f₀ fc a b xs lam nu = f₀ xs :=
      le_antisymm (lagrangian_le_objective xs hfeas lam hlam nu) (hobj_le_L xs)
    constructor
    · intro lam' hlam' nu'
      calc
        lagrangian f₀ fc a b xs lam' nu' ≤ f₀ xs :=
          lagrangian_le_objective xs hfeas lam' hlam' nu'
        _ = lagrangian f₀ fc a b xs lam nu := hL_eq.symm
    · intro x
      calc
        lagrangian f₀ fc a b xs lam nu = f₀ xs := hL_eq
        _ ≤ lagrangian f₀ fc a b x lam nu := hobj_le_L x
