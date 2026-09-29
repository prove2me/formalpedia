-- Prove2me | solution 1 for mme_logarithmic_regional_recipe_compilation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T20:08:25.741975+00:00
-- url     : https://prove2.me/submissions/bbc28a7e-9d64-4d20-a464-fe74bf24d467

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_integer_regional_certified_log_copy_bound
import Mathlib
open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem solution {N ell : ℕ} {P : Predicate N} (D : LogRecipe N ell P) :
    ∃ A : EntropyRecipe N ell P,
      A.inputs = D.inputs ∧ Real.exp D.logOutputs ≤ (A.outputs : ℝ) ∧ A.dims = D.dims := by
  classical
  induction D with
  | boundary B =>
      refine ⟨.boundary B,rfl,?_,rfl⟩
      simp [LogRecipe.logOutputs,EntropyRecipe.outputs]
  | @descend N ell lower P Q level types rate rate_nonneg steps budget inside cover next ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      have hc (j : Fin types) : ⌈Real.exp rate⌉₊ ≤ (steps j).entropyCopies := by
        apply Nat.ceil_le.mpr
        exact mme_integer_regional_certified_log_copy_bound (steps j) rate rate_nonneg (budget j)
      let B := EntropyRecipe.descend level types ⌈Real.exp rate⌉₊ steps hc inside cover A
      refine ⟨B,?_,?_,?_⟩
      · simp only [B,EntropyRecipe.inputs,LogRecipe.inputs,hAi]
      · simp only [B,EntropyRecipe.outputs,LogRecipe.logOutputs,Real.exp_add,Nat.cast_mul]
        exact mul_le_mul (Nat.le_ceil _) hAo (Real.exp_pos _).le (Nat.cast_nonneg _)
      · exact hAd
  | partition size positions Q inside children ih =>
      choose A hAi hAo hAd using ih
      let B := EntropyRecipe.partition size positions Q inside A
      refine ⟨B,?_,?_,?_⟩
      · simp only [B,EntropyRecipe.inputs,LogRecipe.inputs,hAi]
      · simp only [B,EntropyRecipe.outputs,LogRecipe.logOutputs,Real.exp_sum,Nat.cast_prod]
        exact Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) (fun j _ ↦ hAo j)
      · simp only [B,EntropyRecipe.dims,LogRecipe.dims,hAd]
  | rotate child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.rotate A,hAi,hAo,?_⟩
      simp only [EntropyRecipe.dims,LogRecipe.dims,hAd]
  | swap child ih =>
      obtain ⟨A,hAi,hAo,hAd⟩ := ih
      refine ⟨.swap A,hAi,hAo,?_⟩
      simp only [EntropyRecipe.dims,LogRecipe.dims,hAd]
