-- Prove2me | solution 1 for mme_released_recursive_profile_counts_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:05:46.705071+00:00
-- url     : https://prove2.me/submissions/dfafb7ef-d826-4fee-a52a-33de048244c5

import Theorems.Thm_mme_released_recursive_profile_counts_1_mode_0
import Theorems.Thm_mme_released_recursive_profile_counts_1_mode_1
import Theorems.Thm_mme_released_recursive_profile_counts_1_mode_2
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
attribute [local irreducible] jointRows atom parentCount term roles

theorem solution : ∀ (s : Fin 45) (i : Fin 3) (w : Word),
    ((jointRows 1 s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term 1 s) (roles 1 i) w := by
  intro s i w
  fin_cases i
  · exact mme_released_recursive_profile_counts_1_mode_0 s w
  · exact mme_released_recursive_profile_counts_1_mode_1 s w
  · exact mme_released_recursive_profile_counts_1_mode_2 s w
