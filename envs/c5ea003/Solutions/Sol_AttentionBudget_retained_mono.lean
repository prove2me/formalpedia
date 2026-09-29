-- Prove2me | solution 1 for AttentionBudget.retained_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:18:36.279415+00:00
-- url     : https://prove2.me/submissions/f12503cc-9632-4a34-a20c-0e591eb908bf

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_headMass_mono
import Theorems.Thm_AttentionBudget_headMass_nonneg

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw

open AttentionBudget in
lemma solution (n : ℕ) : Monotone (retained w n) := by
  intro a b hab
  exact div_le_div_of_nonneg_right (headMass_mono hw (min_le_min hab le_rfl))
    (headMass_nonneg hw n)
