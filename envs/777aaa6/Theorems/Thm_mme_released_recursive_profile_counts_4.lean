-- Prove2me | Theorems.Thm_mme_released_recursive_profile_counts_4
-- name    : mme_released_recursive_profile_counts_4
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:17.567407+00:00
-- url     : https://prove2.me/theorems/5c0ba05c-7390-4344-9015-59d23d7e0250
-- title:
--   Exact recursive reconstruction of global owner 4
-- statement:
--   For global owner $o=4$, every one of its 45 parent shapes $s$, each hash mode $i$, and every four-letter word $w$, the published supported-joint marginal equals the recursive reconstruction from the published primitive seed:
--   $$\sum_{a:\operatorname{word}_i(a)=w}J_{o,s}(a)=C_{t(o,s)}(r_o(i),w).$$
--   Here $r_o$ maps hash modes to physical modes and $t(o,s)$ uses the published source-shape permutation. The right side explicitly combines six regional split mixtures of square-child profiles, or the primitive boundary profile, all with integer denominator $D^4$. No externally generated reconstruction table is assumed.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_counts_4 : ∀ (s : Fin 45) (i : Fin 3) (w : Word),
    ((jointRows 4 s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term 4 s) (roles 4 i) w := by sorry
