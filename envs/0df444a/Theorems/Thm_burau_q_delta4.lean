-- Prove2me | Theorems.Thm_burau_q_delta4
-- name    : burau_q_delta4
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:33:47.900996+00:00
-- url     : https://prove2.me/theorems/17a0a2ad-2e84-494e-abaf-87fe7eddd2ce
-- title:
--   The full twist squared is trivial in the reduced braid group
-- statement:
--   **The full twist squared is trivial in the reduced braid group.** In
--   $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$, where $\Delta^4=(\sigma_0\sigma_1)^6$, the class of
--   $\Delta^4$ is the identity:
--   $$ \overline{\Delta^4} = 1 . $$
--   This is the defining relation of the reduced group $Q$ and the reason $\Delta^4$ is the expected
--   generator of the kernel of the reduced Burau representation.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem burau_q_delta4 :
    ((BurauNC.Delta4 : BurauNC.B3) : BurauNC.Q) = 1 := by sorry
