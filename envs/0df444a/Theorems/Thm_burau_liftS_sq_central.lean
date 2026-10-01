-- Prove2me | Theorems.Thm_burau_liftS_sq_central
-- name    : burau_liftS_sq_central
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:37:50.760984+00:00
-- url     : https://prove2.me/theorems/10b203cd-0571-4d27-8059-294c2b71de95
-- title:
--   The square of the lifted S-generator is central
-- statement:
--   **Centrality of $\mathrm{liftS}^2$.** In the reduced braid group
--   $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$ the element $\mathrm{liftS}^2$ is central:
--   $$ \mathrm{liftS}^2 \in Z(Q). $$
--   Its preimage is the square of the Garside element of $B_3$, which is central there because it equals
--   $(\sigma_0\sigma_1)^3$; centrality descends through the quotient map. This is what lets the conjugating
--   moves in the Coxeter relation be performed inside a single flat product.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary
import Theorems.Thm_BurauFaithful_braid_three_fullTwist_central

set_option autoImplicit false

theorem burau_liftS_sq_central :
    BurauNC.liftS ^ 2 ∈ Subgroup.center BurauNC.Q := by sorry
