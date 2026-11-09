-- Prove2me | Theorems.Thm_Couret_S5_rank_row_217
-- name    : Couret.S5.rank_row_217
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:12:32.885779+00:00
-- url     : https://prove2.me/theorems/bad466e0-199f-4496-8db6-0eece4ca896a
-- title:
--   Subproduct rank certificate at mask 217
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=217$,
--
--   $$r(217)\le5,\qquad r(217)=5\Longleftrightarrow 1\text{ belongs to mask }217,\qquad \min(r(217)+1,5)\le r(\sigma(217,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock13.lean, lines 16–16; source file SHA-256 459ec068eceb18493966b260925716bbfcf7ed2d8dc30afa4c14f69b504a59fe; theorem Couret.S5.rank_row_217

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_217 : RankFacts 217 := by sorry







end S5
end Couret
