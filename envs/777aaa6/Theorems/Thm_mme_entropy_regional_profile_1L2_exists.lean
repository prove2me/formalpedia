-- Prove2me | Theorems.Thm_mme_entropy_regional_profile_1L2_exists
-- name    : mme_entropy_regional_profile_1L2_exists
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:11:40.626542+00:00
-- url     : https://prove2.me/theorems/da4d3c94-0ce8-41b8-aa4c-e3628114149a
-- title:
--   Level-one profile with dimension 25
-- statement:
--   There is a level-one boundary profile on two positions with dimension $25$.
--
--   The index is $1$ with the count concentrated twice on the all-ones word (multinomial $1$, $5$-power $5^2$). This is the dims-$25$ building block at the levels that actually occur at $N=2$.
--
--   **Formalization Note** All side conditions and the dimension identity hold by computation.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6; level-one analogue of mme_entropy_regional_profile_11_exists.

import Definitions.Def_mme_recursive_yz_boundary_data
set_option autoImplicit false

theorem mme_entropy_regional_profile_1L2_exists : exists (prof : MME.RecursiveYZ.Boundary.Profile 1 2), prof.dim = 25 := by sorry
