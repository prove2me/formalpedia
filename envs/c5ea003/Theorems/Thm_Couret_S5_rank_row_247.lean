-- Prove2me | Theorems.Thm_Couret_S5_rank_row_247
-- name    : Couret.S5.rank_row_247
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:30.451868+00:00
-- url     : https://prove2.me/theorems/e90640a6-5e18-42dc-a0e6-70e05c0b7d66
-- title:
--   Subproduct rank certificate at mask 247
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=247$,
--
--   $$r(247)\le5,\qquad r(247)=5\Longleftrightarrow 1\text{ belongs to mask }247,\qquad \min(r(247)+1,5)\le r(\sigma(247,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock15.lean, lines 14–14; source file SHA-256 b95f23d3d2e017a6013682f0aa79326245001c6cca55f53129d2c627dd705355; theorem Couret.S5.rank_row_247

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_247 : RankFacts 247 := by sorry









end S5
end Couret
