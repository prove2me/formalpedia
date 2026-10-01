-- Prove2me | Theorems.Thm_burau_liftU_cube
-- name    : burau_liftU_cube
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:45:28.464368+00:00
-- url     : https://prove2.me/theorems/664055ee-33eb-46b6-98f2-5df9fbeb62d5
-- title:
--   Coxeter relation (T S)^3 = S^2 in the reduced braid group
-- statement:
--   **Coxeter relation $(\mathrm{liftT}\cdot\mathrm{liftS})^3=\mathrm{liftS}^2$.** With
--   $\mathrm{liftS}=\overline{\sigma_0^2\sigma_1}$ and $\mathrm{liftT}=\overline{\sigma_0^{-1}}$ the images of
--   the standard generators $S,T$ of $\mathrm{SL}(2,\mathbb Z)$,
--   $$ (\mathrm{liftT}\cdot \mathrm{liftS})^3 = \mathrm{liftS}^2 , $$
--   which is the image of the dictionary identity $\mathrm{uLift}^3=\mathrm{sLift}^2$ for the elements
--   $\sigma_0\sigma_1$ and the half twist. Together with $\mathrm{liftS}^4=1$ this is the Coxeter presentation
--   of the quotient.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_braid_three_amalgam_dictionary

set_option autoImplicit false

theorem burau_liftU_cube :
    (BurauNC.liftT * BurauNC.liftS) ^ 3 = BurauNC.liftS ^ 2 := by sorry
