-- Prove2me | Theorems.Thm_mme_released_116_six_region_joint_counts_exact
-- name    : mme_released_116_six_region_joint_counts_exact
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:59:16.295853+00:00
-- url     : https://prove2.me/theorems/8ed5e41a-176e-440a-9411-af0f6578cfa4
-- title:
--   Exact six-region reconstruction of the released (1,1,6) joint counts
-- statement:
--   For owner zero and component (1,1,6), the released joint-count row equals the sum of the six region-weighted split distributions and independent square-child products from the released rational seed. Each region retains its own (1,1,2) child parameter. Repeated base-six atom indices are combined and sorted. The equality is at the exact integer scale denominator^4 and covers the entire joint-count row. This is a data identity; it makes no tensor-realization or global-rate assertion.
-- source:
--   Released exact profile seed, owner zero term 10, and released global joint counts row 10.

import Definitions.Def_mme_released_116_six_region_reconstruction

theorem mme_released_116_six_region_joint_counts_exact :
 MME.Released116.reconstructed = (MME.ReleasedGlobal.jointRows 0 10).map (fun p => (p.1.val, p.2)) := by sorry
