-- Prove2me | solution 1 for mme_released_global_physical_orientation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:18.814128+00:00
-- url     : https://prove2.me/submissions/33af1640-ef50-4cc9-bd18-93edc0cc42d5

import Definitions.Def_mme_released_global_joint_interface
open MME MME.ProfiledCW MME.GlobalCW MME.ReleasedGlobal
set_option autoImplicit false

theorem solution :
    (∀ (o : Fin 6) (i : Fin 3),
      roles o (hashMode o i) = i ∧ hashMode o (roles o i) = i) ∧
    ∀ {M ell : ℕ} {P : Predicate M} (o : Fin 6) (S : Part M ell P),
      (physicalPart o S).inputs = S.inputs ∧
      (physicalPart o S).rate = S.rate := by
  constructor
  · decide +kernel
  · intro M ell P o S
    fin_cases o <;> exact ⟨rfl,rfl⟩
