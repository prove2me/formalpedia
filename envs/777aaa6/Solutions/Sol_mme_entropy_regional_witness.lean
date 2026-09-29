-- Prove2me | solution 1 for mme_entropy_regional_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T12:41:23.796479+00:00
-- url     : https://prove2.me/submissions/5f94824a-65d0-4b0f-8ad6-61066c2ab746
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_entropy_regional_step_five_copies
import Theorems.Thm_mme_entropy_regional_boundary_match
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem solution : ∃ (ell : ℕ) (P : Predicate 2) (D : EntropyRecipe 2 ell P), D.inputs = 1 ∧ D.outputs = 5 ∧ D.a * D.b * D.c = 25 ∧ 1 ≤ D.a * D.b * D.c := by
  obtain ⟨lower, S, h5⟩ := mme_entropy_regional_step_five_copies
  obtain ⟨B, hdims, hpos⟩ := mme_entropy_regional_boundary_match lower S
  -- descend returns `EntropyRecipe N ell P` (the steps' predicate), while the
  -- boundary predicate `Q := S.output` lives only at the lower level.
  let hD : EntropyRecipe 2 (lower + 1) (fun _ _ ↦ True) :=
    EntropyRecipe.descend (N := 2) (ell := lower + 1) (lower := lower)
      (P := fun _ _ ↦ True) (Q := S.output)
      (by omega) 1 5 (fun _ ↦ S) (fun j ↦ h5)
      (fun j i x h ↦ h)
      (fun x _ hxQ ↦ ⟨0, fun i ↦ hxQ i, fun y _ ↦ Fin.ext (Nat.lt_one_iff.mp y.2)⟩)
      (.boundary B)
  refine ⟨lower + 1, _, hD, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact hdims
  · exact hpos
