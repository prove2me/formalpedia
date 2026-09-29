-- Prove2me | Theorems.Thm_mme_dwz_positive_242_regional_rate_lower
-- name    : mme_dwz_positive_242_regional_rate_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:01:58.645744+00:00
-- url     : https://prove2.me/theorems/9d939702-5dba-472e-9c5f-17d62b31840d
-- title:
--   Positive component 242: regional rate lower bound
-- statement:
--   For the six-region integer fine profiles of the DWZ $(2,4,2)$ candidate, let $N$ be their total block count and let $E$ be the explicit entropy expression computed from their rational coarse, parent-word, and compatibility-part distributions. In the coarse branch, $E$ subtracts the weighted gap between the public recursive maximum-entropy upper bound of each regional parent (witnesses 27, 28, 29 of `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropy of the actual split distribution. Then the regional rate used by the integer tensor extraction construction satisfies
--   $$R(N,m,\mu)\ge N E.$$
--   Here $R$ is the existing regional extraction rate, including its coarse entropy, recursive coarse penalty, joint parent-word entropy, and both boundary/interior compatibility potentials. The parent-word and compatibility branches are matched exactly; the coarse branch uses the witness bound on the recursive entropy penalty of the non-thin parent splits. It does not assume a child tensor value.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-160 data generated from the released q=5 fourth-power certificate.

import Theorems.Thm_mme_dwz_positive_242_integer_fine_profile_validity
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero
import Theorems.Thm_mme_dwz_fourth_recursive_entropy_upper

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.DWZ242Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem mme_dwz_positive_242_regional_rate_lower :
    (totalCount : ℝ) * explicitRate ≤ regionalRate parent_total n m mu := by sorry
