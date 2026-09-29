-- Prove2me | Theorems.Thm_mme_released_recursive_profile_counts_0_mode_0
-- name    : mme_released_recursive_profile_counts_0_mode_0
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T16:53:07.420177+00:00
-- url     : https://prove2.me/theorems/68433c17-b154-4c8b-97ea-4d92c4cd0f13
-- title:
--   Exact recursive reconstruction for global owner 0, mode 0
-- statement:
--   For owner $o=0$ and hash mode $i=0$, for all 45 parent shapes and all 81 four-letter words, the published sparse joint marginal equals the physical recursive mixture from the primitive seed, with exact denominator $D^4$. This is one mode of the full owner reconstruction, separated to keep kernel verification within the server time limit.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_counts_0_mode_0 : ∀ (s : Fin 45) (w : Word),
    ((jointRows 0 s).map (fun a ↦ if atom a.1 0 = w then a.2 else 0)).sum =
      parentCount (term 0 s) (roles 0 0) w := by sorry
