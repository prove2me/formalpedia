-- Prove2me | Theorems.Thm_Couret_S5_rank_row_12
-- name    : Couret.S5.rank_row_12
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:08:14.274948+00:00
-- url     : https://prove2.me/theorems/fafebaf0-71fd-4940-b2a3-6992b7c4a492
-- title:
--   Subproduct rank certificate at mask 12
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=12$,
--
--   $$r(12)\le5,\qquad r(12)=5\Longleftrightarrow 1\text{ belongs to mask }12,\qquad \min(r(12)+1,5)\le r(\sigma(12,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock00.lean, lines 19–19; source file SHA-256 5b5b79d47dbea03302241f73ec335797269838fe2f41d74a323693005f369d9b; theorem Couret.S5.rank_row_12

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_12 : RankFacts 12 := by sorry




end S5
end Couret
