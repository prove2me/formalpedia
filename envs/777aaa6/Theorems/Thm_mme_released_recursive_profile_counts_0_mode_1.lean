-- Prove2me | Theorems.Thm_mme_released_recursive_profile_counts_0_mode_1
-- name    : mme_released_recursive_profile_counts_0_mode_1
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T16:52:08.53959+00:00
-- url     : https://prove2.me/theorems/69b0db1a-c73c-4731-804e-9ae092701d85
-- title:
--   Exact recursive reconstruction for global owner 0, mode 1
-- statement:
--   For owner $o=0$ and hash mode $i=1$, for all 45 parent shapes and all 81 four-letter words, the published sparse joint marginal equals the physical recursive mixture from the primitive seed, with exact denominator $D^4$. This is one mode of the full owner reconstruction, separated to keep kernel verification within the server time limit.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_counts_0_mode_1 : ∀ (s : Fin 45) (w : Word),
    ((jointRows 0 s).map (fun a ↦ if atom a.1 1 = w then a.2 else 0)).sum =
      parentCount (term 0 s) (roles 0 1) w := by sorry
