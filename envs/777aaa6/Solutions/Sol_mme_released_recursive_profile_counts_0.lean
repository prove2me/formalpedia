-- Prove2me | solution 1 for mme_released_recursive_profile_counts_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:05:45.426986+00:00
-- url     : https://prove2.me/submissions/fcdec12e-3dc4-4bb8-8935-789b644f92f9

import Theorems.Thm_mme_released_recursive_profile_counts_0_mode_0
import Theorems.Thm_mme_released_recursive_profile_counts_0_mode_1
import Theorems.Thm_mme_released_recursive_profile_counts_0_mode_2
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
attribute [local irreducible] jointRows atom parentCount term roles

theorem solution : ∀ (s : Fin 45) (i : Fin 3) (w : Word),
    ((jointRows 0 s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term 0 s) (roles 0 i) w := by
  intro s i w
  fin_cases i
  · exact mme_released_recursive_profile_counts_0_mode_0 s w
  · exact mme_released_recursive_profile_counts_0_mode_1 s w
  · exact mme_released_recursive_profile_counts_0_mode_2 s w
