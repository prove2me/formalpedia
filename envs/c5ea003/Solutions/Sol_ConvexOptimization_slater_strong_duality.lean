-- Prove2me | solution 1 for ConvexOptimization.slater_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T14:09:53.465441+00:00
-- url     : https://prove2.me/submissions/c53a1247-8711-4df5-91b8-38c7d4835916

import Theorems.Thm_ConvexOptimization_slater_supporting_multipliers

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_ineq : ∀ i, fc i xs < 0)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' feasibleSet fc a b)) :
    ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧
      dualFunction f₀ fc a b lam nu =
        ((sInf (f₀ '' feasibleSet fc a b) : ℝ) : EReal) := by
  obtain ⟨lam, nu, hlam, hsupport⟩ :=
    slater_supporting_multipliers f₀ hf₀ fc hfc a ha b xs hxs_ineq hxs_eq hbdd
  refine ⟨lam, nu, hlam, ?_⟩
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x => lagrangian f₀ fc a b x lam nu
  let pstar : ℝ := sInf (f₀ '' feasibleSet fc a b)
  have hL_lower (x : EuclideanSpace ℝ (Fin n)) : pstar ≤ L x := hsupport x
  have hL_bdd : BddBelow (Set.range L) := by
    refine ⟨pstar, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hL_lower x
  have hL_top_bdd : BddBelow (Set.range fun x => (L x : WithTop ℝ)) := by
    refine ⟨(pstar : WithTop ℝ), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact WithTop.coe_le_coe.mpr (hL_lower x)
  have hfeas : xs ∈ feasibleSet fc a b := ⟨fun i => (hxs_ineq i).le, hxs_eq⟩
  have himage : (f₀ '' feasibleSet fc a b).Nonempty := ⟨f₀ xs, xs, hfeas, rfl⟩
  have hweak (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ feasibleSet fc a b) :
      L x ≤ f₀ x := by
    have hi : (∑ i, lam i * fc i x) ≤ 0 := by
      exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hx.1 i)
    have heq : (∑ j, nu j * (⟪a j, x⟫ - b j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx.2 j, sub_self, mul_zero]
    dsimp [L]
    simp only [lagrangian, heq, add_zero]
    linarith
  have hiInf_eq : (⨅ x, L x) = pstar := by
    apply le_antisymm
    · apply le_csInf himage
      rintro _ ⟨x, hx, rfl⟩
      exact (ciInf_le hL_bdd x).trans (hweak x hx)
    · exact le_ciInf hL_lower
  change (⨅ x, ((L x : WithTop ℝ) : WithBot (WithTop ℝ))) =
    ((pstar : WithTop ℝ) : WithBot (WithTop ℝ))
  rw [← WithBot.coe_iInf (fun x => (L x : WithTop ℝ)) hL_top_bdd]
  rw [← WithTop.coe_iInf hL_bdd, hiInf_eq]
