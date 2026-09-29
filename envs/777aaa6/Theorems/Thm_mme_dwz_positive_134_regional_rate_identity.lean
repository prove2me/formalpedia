-- Prove2me | Theorems.Thm_mme_dwz_positive_134_regional_rate_identity
-- name    : mme_dwz_positive_134_regional_rate_identity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-20T20:08:11.281453+00:00
-- url     : https://prove2.me/theorems/5458b9c2-6104-45bb-9774-aad938abb2bf
-- title:
--   The concrete DWZ (1,3,4) entropy formula is the integer regional extraction rate
-- statement:
--   For the six-region integer fine profiles of the DWZ $(1,3,4)$ candidate, let $N$ be their total block count and let $E$ be the explicit entropy expression computed from their rational coarse, parent-word, and compatibility-part distributions. Then the regional rate used by the integer tensor extraction construction is exactly
--   $$R(N,m,\mu)=N E.$$
--   Here $R$ is the existing regional extraction rate, including its coarse entropy, coarse compatibility penalty, joint parent-word entropy, and both boundary/interior compatibility potentials. The identity connects the explicit numerical entropy calculation to that existing construction. It does not require an entropy inequality or assume a child tensor value.
-- source:
--   Original exact reindexing and normalization of mme_regional_entropy_rate_data for the concrete profiles mme_dwz_positive_134_integer_fine_profile_data. Uses the proved profile validity, homogeneous mass-entropy algebra, and zero coarse penalty for thin parent splits.

import Theorems.Thm_mme_dwz_positive_134_integer_fine_profile_validity
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.DWZ134Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem mme_dwz_positive_134_regional_rate_identity :
    regionalRate parent_total n m mu = (totalCount : ℝ) * explicitRate := by sorry
