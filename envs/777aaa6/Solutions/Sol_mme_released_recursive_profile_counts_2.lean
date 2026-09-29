-- Prove2me | solution 1 for mme_released_recursive_profile_counts_2
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:05:50.605965+00:00
-- url     : https://prove2.me/submissions/13708656-2c50-420f-8417-19fa0a39c3f3

import Theorems.Thm_mme_released_recursive_profile_counts_2_mode_0
import Theorems.Thm_mme_released_recursive_profile_counts_2_mode_1
import Theorems.Thm_mme_released_recursive_profile_counts_2_mode_2
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
attribute [local irreducible] jointRows atom parentCount term roles

theorem solution : ∀ (s : Fin 45) (i : Fin 3) (w : Word),
    ((jointRows 2 s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term 2 s) (roles 2 i) w := by
  intro s i w
  fin_cases i
  · exact mme_released_recursive_profile_counts_2_mode_0 s w
  · exact mme_released_recursive_profile_counts_2_mode_1 s w
  · exact mme_released_recursive_profile_counts_2_mode_2 s w
