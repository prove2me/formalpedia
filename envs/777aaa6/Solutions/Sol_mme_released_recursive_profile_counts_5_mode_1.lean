-- Prove2me | solution 1 for mme_released_recursive_profile_counts_5_mode_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:31:52.550415+00:00
-- url     : https://prove2.me/submissions/5b6ffc5c-d5dd-47ad-a1fc-8c5f81222de4

import Theorems.Thm_mme_released_recursive_profile_counts_5_mode_1_low
import Theorems.Thm_mme_released_recursive_profile_counts_5_mode_1_high
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
attribute [local irreducible] jointRows atom parentCount term roles

theorem solution : ∀ (s : Fin 45) (w : Word),
    ((jointRows 5 s).map (fun a ↦ if atom a.1 1 = w then a.2 else 0)).sum =
      parentCount (term 5 s) (roles 5 1) w := by
  intro s w
  by_cases hs : s.val < 23
  · exact mme_released_recursive_profile_counts_5_mode_1_low s hs w
  · exact mme_released_recursive_profile_counts_5_mode_1_high s (Nat.le_of_not_gt hs) w
