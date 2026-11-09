-- Prove2me | Theorems.Thm_Couret_S5_rank_row_144
-- name    : Couret.S5.rank_row_144
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:11.164198+00:00
-- url     : https://prove2.me/theorems/50aaee51-1ec5-4368-ab06-86fe7a0f75cc
-- title:
--   Subproduct rank certificate at mask 144
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=144$,
--
--   $$r(144)\le5,\qquad r(144)=5\Longleftrightarrow 1\text{ belongs to mask }144,\qquad \min(r(144)+1,5)\le r(\sigma(144,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock09.lean, lines 7–7; source file SHA-256 cf82452ae772ea8b3c462b4573a0213fc3b411e420f2f7e6970c57e7d682703c; theorem Couret.S5.rank_row_144

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_144 : RankFacts 144 := by sorry
















end S5
end Couret
