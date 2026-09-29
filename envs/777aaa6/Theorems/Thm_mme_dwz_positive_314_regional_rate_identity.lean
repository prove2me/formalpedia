-- Prove2me | Theorems.Thm_mme_dwz_positive_314_regional_rate_identity
-- name    : mme_dwz_positive_314_regional_rate_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T15:36:05.801119+00:00
-- url     : https://prove2.me/theorems/908bddbe-c00d-4ee9-b133-b6799fb8734e
-- title:
--   Positive component 314: regional rate identity
-- statement:
--   For the six-region integer fine profiles of the DWZ $(3,1,4)$ candidate, let $N$ be their total block count and let $E$ be the explicit entropy expression computed from their rational coarse, parent-word, and compatibility-part distributions. Then the regional rate used by the integer tensor extraction construction is exactly
--   $$R(N,m,\mu)=N E.$$
--   Here $R$ is the existing regional extraction rate, including its coarse entropy, coarse compatibility penalty, joint parent-word entropy, and both boundary/interior compatibility potentials. The identity connects the explicit numerical entropy calculation to that existing construction. It does not require an entropy inequality or assume a child tensor value.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-164 data generated from the released q=5 fourth-power certificate.

import Theorems.Thm_mme_dwz_positive_314_integer_fine_profile_validity
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.DWZ314Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem mme_dwz_positive_314_regional_rate_identity :
    regionalRate parent_total n m mu = (totalCount : ℝ) * explicitRate := by sorry
