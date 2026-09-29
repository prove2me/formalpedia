-- Prove2me | solution 1 for mme_entropy_regional_recipe_compilation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:30:10.767234+00:00
-- url     : https://prove2.me/submissions/d444b75d-8477-4353-8a38-51cbf1460be8

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_integer_regional_entropy_copy_bound
open BigOperators MME MME.ProfiledCW MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem solution {N ell : ℕ} {P : Predicate N} (D : EntropyRecipe N ell P) :
    ∃ A : IntegerRecipe N ell P,
      A.inputs = D.inputs ∧ A.outputs = D.outputs ∧ A.dims = D.dims := by
  classical
  induction D with
  | boundary B => exact ⟨.boundary B,rfl,rfl,rfl⟩
  | @descend N ell lower P Q level types copies steps enough inside cover next ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      let B := IntegerRecipe.descend level types copies steps
        (fun j ↦ (enough j).trans (mme_integer_regional_entropy_copy_bound (steps j)).2) inside cover A
      refine ⟨B,?_,?_,?_⟩
      · simp only [B,IntegerRecipe.inputs,EntropyRecipe.inputs,hAi]
      · simp only [B,IntegerRecipe.outputs,EntropyRecipe.outputs,hAo]
      · exact hAd
  | partition size positions Q inside children ih =>
      choose A hAi hAo hAd using ih
      let B := IntegerRecipe.partition size positions Q inside A
      refine ⟨B,?_,?_,?_⟩
      · simp only [B,IntegerRecipe.inputs,EntropyRecipe.inputs,hAi]
      · simp only [B,IntegerRecipe.outputs,EntropyRecipe.outputs,hAo]
      · simp only [B,IntegerRecipe.dims,EntropyRecipe.dims,hAd]
  | rotate child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.rotate A,hAi,hAo,?_⟩
      simp only [IntegerRecipe.dims,EntropyRecipe.dims,hAd]
  | swap child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.swap A,hAi,hAo,?_⟩
      simp only [IntegerRecipe.dims,EntropyRecipe.dims,hAd]
