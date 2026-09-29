-- Prove2me | solution 1 for mme_log_joint_recipe_g_stage_compose
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:02:20.456089+00:00
-- url     : https://prove2.me/submissions/973603de-9cee-4df7-8940-a53d641de7c3

import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution {N ell lower parts : ℕ} {P Q : Predicate N}
    (level_decreases : lower < ell)
    (size : Fin parts → ℕ)
    (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (S T : ∀ j, Predicate (size j))
    (source : ∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j, r⟩))) → P i x)
    (steps : ∀ j, LogPartStageG (size j) lower (S j) (T j))
    (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩)))
    (next : LogJointRecipeG N lower Q)
    (X Y : ℕ) (α β : ℝ)
    (htypes : ∀ j, 1 ≤ (steps j).types ∧ (steps j).types ≤ X)
    (hnext1 : 1 ≤ next.inputs) (hnextY : next.inputs ≤ Y)
    (hα : α ≤ ∑ j, (steps j).rate) (hβ : β ≤ next.logOutputs) :
    ∃ R : LogJointRecipeG N ell P,
      1 ≤ R.inputs ∧ R.inputs ≤ X ^ parts * Y ∧
      α + β ≤ R.logOutputs ∧
      R.a = next.a ∧ R.b = next.b ∧ R.c = next.c := by
  refine ⟨LogJointRecipeG.stage level_decreases size positions S T source steps target next,
    ?_, ?_, ?_, rfl, rfl, rfl⟩
  · show 1 ≤ (∏ j, (steps j).types) * next.inputs
    have h1 : 1 ≤ ∏ j, (steps j).types := by
      rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro j _
      have := (htypes j).1
      omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · show (∏ j, (steps j).types) * next.inputs ≤ X ^ parts * Y
    have h1 : ∏ j, (steps j).types ≤ X ^ parts := by
      calc ∏ j, (steps j).types ≤ ∏ _j : Fin parts, X :=
            Finset.prod_le_prod' (fun j _ ↦ (htypes j).2)
        _ = X ^ parts := by simp
    exact Nat.mul_le_mul h1 hnextY
  · show α + β ≤ (∑ j, (steps j).rate) + next.logOutputs
    linarith
