-- Prove2me | solution 1 for mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:23:31.98309+00:00
-- url     : https://prove2.me/submissions/abd01977-a99e-44f3-8701-4b7ab6ae0c56

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data

open MME MME.CompleteSplit MME.DWZSimultaneous BigOperators

set_option autoImplicit false
set_option warningAsError true



/-- Ownership depends only on the coarse grade and chosen profile tag at each
position, never on a choice of atomic representative inside such a block. -/
theorem solution
    {C W : Type*} [DecidableEq C] [DecidableEq W] {ell N k : ℕ}
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (f g : FineWord ell N)
    (hgrade : ∀ t, (∑ r, (f t r).val) = ∑ r, (g t r).val)
    (htag : ∀ t, tag (f t) = tag (g t)) :
    (∀ j i, Graded component shape j i f ↔ Graded component shape j i g) ∧
    (∀ j i, Profile component tag mu j i f ↔ Profile component tag mu j i g) ∧
    (∀ j, ZCompatible component shape tag mu j f ↔
      ZCompatible component shape tag mu j g) ∧
    (∀ j i, Allowed component shape tag mu j i f ↔
      Allowed component shape tag mu j i g) := by
  have hg (j : Fin k) (i : Fin 3) :
      Graded component shape j i f ↔ Graded component shape j i g := by
    simp only [Graded, hgrade]
  have hp (j : Fin k) (i : Fin 3) :
      Profile component tag mu j i f ↔ Profile component tag mu j i g := by
    simp only [DWZSimultaneous.Profile, htag]
  have hz (j : Fin k) : ZCompatible component shape tag mu j f ↔
      ZCompatible component shape tag mu j g := by
    simp only [ZCompatible, hg, htag]
  refine ⟨hg, hp, hz, ?_⟩
  intro j i
  simp only [Allowed, hg, hp, hz, htag]




