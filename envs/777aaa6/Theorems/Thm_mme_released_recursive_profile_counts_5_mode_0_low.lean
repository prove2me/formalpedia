-- Prove2me | Theorems.Thm_mme_released_recursive_profile_counts_5_mode_0_low
-- name    : mme_released_recursive_profile_counts_5_mode_0_low
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T17:27:54.487898+00:00
-- url     : https://prove2.me/theorems/0c610223-17be-4ae2-8bce-ea28e5abde79
-- title:
--   Exact owner-five first-mode reconstruction: low shape range
-- statement:
--   For owner five and hash mode zero, the exact global joint marginal equals the primitive recursive mixture on the indicated range of parent shape indices. The low range has indices below 23 and the high range has indices at least 23. Together they cover all 45 shapes and every four-letter word.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_counts_5_mode_0_low : ∀ (s : Fin 45), s.val < 23 → ∀ (w : Word),
    ((jointRows 5 s).map (fun a ↦ if atom a.1 0 = w then a.2 else 0)).sum =
      parentCount (term 5 s) (roles 5 0) w := by sorry
