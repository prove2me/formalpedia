-- Prove2me | solution 1 for mme_log_joint_recipe_g_source_mono
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T21:27:17.024985+00:00
-- url     : https://prove2.me/submissions/7d7d26da-6809-408e-bac3-5df901e97b45

import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

private theorem logRecipe_cast {N ell : ℕ} {P Q : Predicate N} (hPQ : P = Q)
    (R : LogRecipe N ell P) :
    ∃ R' : LogRecipe N ell Q,
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by
  subst hPQ; exact ⟨R, rfl, rfl, rfl⟩

private theorem logJointRecipeG_cast {N ell : ℕ} {P Q : Predicate N} (hPQ : P = Q)
    (R : LogJointRecipeG N ell P) :
    ∃ R' : LogJointRecipeG N ell Q,
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by
  subst hPQ; exact ⟨R, rfl, rfl, rfl⟩

/-- Weakening the source predicate of a logarithmic recipe. -/
private theorem logRecipe_source_mono {N ell : ℕ} {P : Predicate N}
    (R : LogRecipe N ell P) : ∀ (P' : Predicate N), (∀ i x, P i x → P' i x) →
    ∃ R' : LogRecipe N ell P',
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by
  induction R with
  | boundary data =>
    intro P' h
    exact ⟨.boundary { data with inside := fun i x hx ↦ h i x (data.inside i x hx) },
      rfl, rfl, rfl⟩
  | descend hlt types rate hrate steps budget inside cover next _ =>
    intro P' h
    let steps' : Fin types → IntegerStep _ _ P' := fun j ↦
      { steps j with source_inside := fun i x hx ↦ h i x ((steps j).source_inside i x hx) }
    exact ⟨.descend hlt types rate hrate steps' budget inside cover next, rfl, rfl, rfl⟩
  | partition size positions Q inside children _ =>
    intro P' h
    exact ⟨.partition size positions Q (fun i x hx ↦ h i x (inside i x hx)) children,
      rfl, rfl, rfl⟩
  | rotate child ih =>
    intro P' h
    obtain ⟨R', h1, h2, h3⟩ := ih (fun i ↦ P' (cyclicPerm i)) (fun i x hx ↦ by
      apply h; simpa using hx)
    obtain ⟨R'', g1, g2, g3⟩ := logRecipe_cast
      (show (fun i ↦ P' (cyclicPerm (cyclicPerm.symm i))) = P' by funext i; simp) R'.rotate
    refine ⟨R'', ?_, ?_, ?_⟩
    · rw [g1]; exact h1
    · rw [g2]; exact h2
    · rw [g3]; simp only [LogRecipe.dims, h3]
  | swap child ih =>
    intro P' h
    obtain ⟨R', h1, h2, h3⟩ := ih (fun i ↦ P' (swapFirstTwoPerm i)) (fun i x hx ↦ by
      apply h; simpa using hx)
    obtain ⟨R'', g1, g2, g3⟩ := logRecipe_cast
      (show (fun i ↦ P' (swapFirstTwoPerm (swapFirstTwoPerm.symm i))) = P' by funext i; simp)
      R'.swap
    refine ⟨R'', ?_, ?_, ?_⟩
    · rw [g1]; exact h1
    · rw [g2]; exact h2
    · rw [g3]; simp only [LogRecipe.dims, h3]

private theorem logJointRecipeG_source_mono {N ell : ℕ} {P : Predicate N}
    (R : LogJointRecipeG N ell P) : ∀ (P' : Predicate N), (∀ i x, P i x → P' i x) →
    ∃ R' : LogJointRecipeG N ell P',
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims := by
  induction R with
  | base data =>
    intro P' h
    obtain ⟨D, h1, h2, h3⟩ := logRecipe_source_mono data P' h
    exact ⟨.base D, h1, h2, h3⟩
  | stage hlt size positions S T source steps target next _ =>
    intro P' h
    exact ⟨.stage hlt size positions S T (fun i x hx ↦ h i x (source i x hx)) steps target next,
      rfl, rfl, rfl⟩
  | partition size positions Q inside children _ =>
    intro P' h
    exact ⟨.partition size positions Q (fun i x hx ↦ h i x (inside i x hx)) children,
      rfl, rfl, rfl⟩
  | rotate child ih =>
    intro P' h
    obtain ⟨R', h1, h2, h3⟩ := ih (fun i ↦ P' (cyclicPerm i)) (fun i x hx ↦ by
      apply h; simpa using hx)
    obtain ⟨R'', g1, g2, g3⟩ := logJointRecipeG_cast
      (show (fun i ↦ P' (cyclicPerm (cyclicPerm.symm i))) = P' by funext i; simp) R'.rotate
    refine ⟨R'', ?_, ?_, ?_⟩
    · rw [g1]; exact h1
    · rw [g2]; exact h2
    · rw [g3]; simp only [LogJointRecipeG.dims, h3]
  | swap child ih =>
    intro P' h
    obtain ⟨R', h1, h2, h3⟩ := ih (fun i ↦ P' (swapFirstTwoPerm i)) (fun i x hx ↦ by
      apply h; simpa using hx)
    obtain ⟨R'', g1, g2, g3⟩ := logJointRecipeG_cast
      (show (fun i ↦ P' (swapFirstTwoPerm (swapFirstTwoPerm.symm i))) = P' by funext i; simp)
      R'.swap
    refine ⟨R'', ?_, ?_, ?_⟩
    · rw [g1]; exact h1
    · rw [g2]; exact h2
    · rw [g3]; simp only [LogJointRecipeG.dims, h3]

theorem solution {N ell : ℕ} {P : Predicate N}
    (R : LogJointRecipeG N ell P) (P' : Predicate N) (h : ∀ i x, P i x → P' i x) :
    ∃ R' : LogJointRecipeG N ell P',
      R'.inputs = R.inputs ∧ R'.logOutputs = R.logOutputs ∧ R'.dims = R.dims :=
  logJointRecipeG_source_mono R P' h
