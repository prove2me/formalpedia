-- Prove2me | Theorems.Thm_Couret_S5_rank_row_196
-- name    : Couret.S5.rank_row_196
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:11:53.654011+00:00
-- url     : https://prove2.me/theorems/2a932ef3-047f-41fc-b23c-7170edcdadd3
-- title:
--   Subproduct rank certificate at mask 196
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=196$,
--
--   $$r(196)\le5,\qquad r(196)=5\Longleftrightarrow 1\text{ belongs to mask }196,\qquad \min(r(196)+1,5)\le r(\sigma(196,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock12.lean, lines 11–11; source file SHA-256 85cc881614c444586af7897c4b5325025e4d7fd22acd168385d4775218f86f16; theorem Couret.S5.rank_row_196

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_196 : RankFacts 196 := by sorry












end S5
end Couret
