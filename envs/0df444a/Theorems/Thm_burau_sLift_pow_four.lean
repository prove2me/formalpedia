-- Prove2me | Theorems.Thm_burau_sLift_pow_four
-- name    : burau_sLift_pow_four
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:56:37.844183+00:00
-- url     : https://prove2.me/theorems/65da2fed-e87b-42b4-8377-b5a49fe5f9dc
-- title:
--   Fourth power of the lifted half twist equals the full twist squared
-- statement:
--   **Fourth power of the lifted half twist.** With $\mathrm{sLift}$ the lift of the half twist
--   in $B_3$, one has
--   $$ \mathrm{sLift}^4 = \Delta^4 = (\sigma_0\sigma_1)^6 , $$
--   because the amalgam dictionary gives $\mathrm{sLift}^2 = (\sigma_0\sigma_1)^3$ and squaring doubles the
--   exponent. This is the elementary computation behind the Coxeter relation $\mathrm{liftS}^4=1$ in the
--   reduced group.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary

set_option autoImplicit false

theorem burau_sLift_pow_four :
    (BurauFaithful.sLift : BurauNC.B3) ^ 4 = BurauNC.Delta4 := by sorry
