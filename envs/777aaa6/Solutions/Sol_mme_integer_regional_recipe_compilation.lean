-- Prove2me | solution 1 for mme_integer_regional_recipe_compilation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:35:19.467755+00:00
-- url     : https://prove2.me/submissions/4d682b65-f82c-4f12-8e0e-65b75db239af

import Definitions.Def_mme_integer_regional_CW_recipe
import Theorems.Thm_mme_integer_regional_step_realization

open BigOperators MME MME.ProfiledCW MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem solution {N ell : ℕ} {P : Predicate N} (D : IntegerRecipe N ell P) :
    ∃ A : RegionalPlan N ell P,
      A.inputs = D.inputs ∧ A.outputs = D.outputs ∧ A.dims = D.dims := by
  classical
  induction D with
  | boundary B => exact ⟨.base (.boundary B),rfl,rfl,rfl⟩
  | @descend N ell lower P Q level types copies steps enough inside cover next ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      have hs j := mme_integer_regional_step_realization (steps j)
      choose E hEc hEo using hs
      have hInside : ∀ j i x, (E j).output i x → Q i x := by
        intro j i x hx
        rw [hEo j] at hx
        exact inside j i x hx
      have hCover : ∀ x, supported x → (∀ i, Q i (x i)) → ∃! j, ∀ i, (E j).output i (x i) := by
        intro x hx hQ
        simp_rw [hEo]
        exact cover x hx hQ
      let B := RegionalPlan.descend level types copies E (fun j ↦ (enough j).trans (hEc j))
        hInside hCover A
      refine ⟨B, ?_, ?_, ?_⟩
      · simp only [B, RegionalPlan.inputs, IntegerRecipe.inputs, hAi]
      · simp only [B, RegionalPlan.outputs, IntegerRecipe.outputs, hAo]
      · exact hAd
  | partition size positions Q inside children ih =>
      choose A hAi hAo hAd using ih
      let B := RegionalPlan.partition size positions Q inside A
      refine ⟨B, ?_, ?_, ?_⟩
      · simp only [B, RegionalPlan.inputs, IntegerRecipe.inputs, hAi]
      · simp only [B, RegionalPlan.outputs, IntegerRecipe.outputs, hAo]
      · simp only [B, RegionalPlan.dims, IntegerRecipe.dims, hAd]
  | rotate child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.rotate A,hAi,hAo,?_⟩
      simp only [RegionalPlan.dims, IntegerRecipe.dims, hAd]
  | swap child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.swap A,hAi,hAo,?_⟩
      simp only [RegionalPlan.dims, IntegerRecipe.dims, hAd]
