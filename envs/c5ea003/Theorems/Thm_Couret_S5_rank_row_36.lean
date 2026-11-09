-- Prove2me | Theorems.Thm_Couret_S5_rank_row_36
-- name    : Couret.S5.rank_row_36
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:14:07.701865+00:00
-- url     : https://prove2.me/theorems/63e6bd7c-f4ee-47f9-8475-26d1f76571de
-- title:
--   Subproduct rank certificate at mask 36
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=36$,
--
--   $$r(36)\le5,\qquad r(36)=5\Longleftrightarrow 1\text{ belongs to mask }36,\qquad \min(r(36)+1,5)\le r(\sigma(36,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock02.lean, lines 11–11; source file SHA-256 892ab82a03f018203ff4eb8a8bebb5d1750d0fb2cf1a92836703e32648dc36b2; theorem Couret.S5.rank_row_36

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_36 : RankFacts 36 := by sorry












end S5
end Couret
