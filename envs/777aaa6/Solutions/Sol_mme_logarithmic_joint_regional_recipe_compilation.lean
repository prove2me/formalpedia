-- Prove2me | solution 1 for mme_logarithmic_joint_regional_recipe_compilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T00:58:25.999572+00:00
-- url     : https://prove2.me/submissions/9c5ecbf1-c186-4401-88f0-b5fa76c674c5

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Theorems.Thm_mme_logarithmic_regional_recipe_compilation
import Theorems.Thm_mme_entropy_regional_recipe_compilation
import Theorems.Thm_mme_integer_regional_recipe_compilation
import Theorems.Thm_mme_integer_regional_certified_log_copy_bound
import Theorems.Thm_mme_integer_regional_entropy_copy_bound
import Theorems.Thm_mme_integer_regional_step_realization
import Theorems.Thm_mme_CW_copied_finite_surplus_omega_bound
import Definitions.Def_mme_joint_regional_CW_plan_data
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
import Mathlib

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RegionRealization
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

private theorem log_part_compile {M lower : ℕ} {S T : Predicate M} (D : LogPartStage M lower S T) :
    ∃ A : PartStage M lower S T, A.types = D.types ∧ Real.exp D.rate ≤ (A.copies : ℝ) := by
  classical
  induction D with
  | @step S T types rate rate_nonneg steps budget inside cover =>
    have hs j := mme_integer_regional_step_realization (steps j)
    choose E hEc hEo using hs
    have hc (j : Fin types) : ⌈Real.exp rate⌉₊ ≤ (E j).copies := by
      apply le_trans _ (hEc j)
      apply le_trans _ (mme_integer_regional_entropy_copy_bound (steps j)).2
      exact Nat.ceil_le.mpr
        (mme_integer_regional_certified_log_copy_bound (steps j) rate rate_nonneg (budget j))
    have hInside : ∀ j i x, (E j).output i x → T i x := by
      intro j i x hx
      rw [hEo j] at hx
      exact inside j i x hx
    have hCover : ∀ x, supported x → (∀ i, T i (x i)) → ∃! j, ∀ i, (E j).output i (x i) := by
      intro x hx hT
      simp_rw [hEo]
      exact cover x hx hT
    exact ⟨.step types ⌈Real.exp rate⌉₊ E hc hInside hCover, rfl, Nat.le_ceil _⟩
  | rotate child ih =>
    obtain ⟨A, hAt, hAc⟩ := ih
    exact ⟨.rotate A, hAt, hAc⟩
  | swap child ih =>
    obtain ⟨A, hAt, hAc⟩ := ih
    exact ⟨.swap A, hAt, hAc⟩

/- Every logarithmic joint recipe compiles to a joint regional plan with the same inputs
and dimensions and at least `exp logOutputs` outputs. -/
theorem solution {N ell : ℕ} {P : Predicate N} (D : LogJointRecipe N ell P) :
    ∃ A : JointPlan N ell P,
      A.inputs = D.inputs ∧ Real.exp D.logOutputs ≤ (A.outputs : ℝ) ∧ A.dims = D.dims := by
  classical
  induction D with
  | base D =>
    obtain ⟨A1, h1i, h1o, h1d⟩ := mme_logarithmic_regional_recipe_compilation D
    obtain ⟨A2, h2i, h2o, h2d⟩ := mme_entropy_regional_recipe_compilation A1
    obtain ⟨A3, h3i, h3o, h3d⟩ := mme_integer_regional_recipe_compilation A2
    refine ⟨.base A3, ?_, ?_, ?_⟩
    · simp only [JointPlan.inputs, LogJointRecipe.inputs, h3i, h2i, h1i]
    · simp only [JointPlan.outputs, LogJointRecipe.logOutputs, h3o, h2o]
      exact h1o
    · simp only [JointPlan.dims, LogJointRecipe.dims, h3d, h2d, h1d]
  | @stage N ell lower parts P Q level size positions S T source steps target next ih =>
    obtain ⟨A, hAi, hAo, hAd⟩ := ih
    choose B hBt hBc using fun j ↦ log_part_compile (steps j)
    refine ⟨.stage level size positions S T source B target A, ?_, ?_, ?_⟩
    · simp only [JointPlan.inputs, LogJointRecipe.inputs, hBt, hAi]
    · simp only [JointPlan.outputs, LogJointRecipe.logOutputs, Real.exp_add, Real.exp_sum,
        Nat.cast_mul, Nat.cast_prod]
      exact mul_le_mul (Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) (fun j _ ↦ hBc j))
        hAo (Real.exp_pos _).le (Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
    · exact hAd
  | partition size positions Q inside children ih =>
    choose A hAi hAo hAd using ih
    refine ⟨.partition size positions Q inside A, ?_, ?_, ?_⟩
    · simp only [JointPlan.inputs, LogJointRecipe.inputs, hAi]
    · simp only [JointPlan.outputs, LogJointRecipe.logOutputs, Real.exp_sum, Nat.cast_prod]
      exact Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) (fun j _ ↦ hAo j)
    · simp only [JointPlan.dims, LogJointRecipe.dims, hAd]
  | rotate child ih =>
    obtain ⟨A, hAi, hAo, hAd⟩ := ih
    refine ⟨.rotate A, hAi, hAo, ?_⟩
    simp only [JointPlan.dims, LogJointRecipe.dims, hAd]
  | swap child ih =>
    obtain ⟨A, hAi, hAo, hAd⟩ := ih
    refine ⟨.swap A, hAi, hAo, ?_⟩
    simp only [JointPlan.dims, LogJointRecipe.dims, hAd]
