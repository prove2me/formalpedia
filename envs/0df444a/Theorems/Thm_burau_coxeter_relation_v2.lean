-- Prove2me | Theorems.Thm_burau_coxeter_relation_v2
-- name    : burau_coxeter_relation_v2
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T23:13:26.980628+00:00
-- url     : https://prove2.me/theorems/8d7f0ffa-3c20-48f6-bf2d-ac6c6dbe41b8
-- title:
--   Coxeter relation (S^-1 T)^3 = 1
-- statement:
--   **Coxeter relation $(\mathrm{liftS}^{-1}\mathrm{liftT})^3=1$.** In the reduced braid group
--   $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$ the two generators
--   $\mathrm{liftS}=\overline{\sigma_0^2\sigma_1}$ and $\mathrm{liftT}=\overline{\sigma_0^{-1}}$ satisfy
--   $$ (\mathrm{liftS}^{-1}\cdot \mathrm{liftT})^3 = 1 . $$
--   With the relations $\mathrm{liftS}^4=1$, $(\mathrm{liftT}\,\mathrm{liftS})^3=\mathrm{liftS}^2$ and the
--   centrality of $\mathrm{liftS}^2$ this is the Coxeter–Moser presentation input for
--   $Q\cong\mathrm{SL}(2,\mathbb Z)$ used in the three-strand Burau faithfulness reduction.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_burau_liftS_pow_four
import Theorems.Thm_burau_liftU_cube
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

theorem burau_coxeter_relation_v2 :
    (BurauNC.liftS⁻¹ * BurauNC.liftT) ^ 3 = 1 := by sorry
