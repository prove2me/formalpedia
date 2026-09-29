-- Prove2me | solution 1 for mme_released_recursive_profile_counts_4
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:53.712654+00:00
-- url     : https://prove2.me/submissions/eab57688-39ad-4223-9af0-17675527315e

import Theorems.Thm_mme_released_recursive_profile_counts_4_mode_0
import Theorems.Thm_mme_released_recursive_profile_counts_4_mode_1
import Theorems.Thm_mme_released_recursive_profile_counts_4_mode_2
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
attribute [local irreducible] jointRows atom parentCount term roles

theorem solution : ∀ (s : Fin 45) (i : Fin 3) (w : Word),
    ((jointRows 4 s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term 4 s) (roles 4 i) w := by
  intro s i w
  fin_cases i
  · exact mme_released_recursive_profile_counts_4_mode_0 s w
  · exact mme_released_recursive_profile_counts_4_mode_1 s w
  · exact mme_released_recursive_profile_counts_4_mode_2 s w
