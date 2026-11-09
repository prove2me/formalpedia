-- Prove2me | Theorems.Thm_Couret_S5_rank_row_147
-- name    : Couret.S5.rank_row_147
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:19.629621+00:00
-- url     : https://prove2.me/theorems/3075e6ba-8f65-4204-81ab-3e665c6d6935
-- title:
--   Subproduct rank certificate at mask 147
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=147$,
--
--   $$r(147)\le5,\qquad r(147)=5\Longleftrightarrow 1\text{ belongs to mask }147,\qquad \min(r(147)+1,5)\le r(\sigma(147,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock09.lean, lines 10–10; source file SHA-256 cf82452ae772ea8b3c462b4573a0213fc3b411e420f2f7e6970c57e7d682703c; theorem Couret.S5.rank_row_147

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_147 : RankFacts 147 := by sorry













end S5
end Couret
