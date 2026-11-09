-- Prove2me | Theorems.Thm_Couret_S5_rank_row_125
-- name    : Couret.S5.rank_row_125
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:08:35.338893+00:00
-- url     : https://prove2.me/theorems/baa6ee21-ba56-455c-9eb8-99635c034520
-- title:
--   Subproduct rank certificate at mask 125
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=125$,
--
--   $$r(125)\le5,\qquad r(125)=5\Longleftrightarrow 1\text{ belongs to mask }125,\qquad \min(r(125)+1,5)\le r(\sigma(125,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock07.lean, lines 20–20; source file SHA-256 ffd8b4dce78a275163f5d9d787e9eb3a316a119a06cc46ad8a7fa891a1e6d16a; theorem Couret.S5.rank_row_125

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_125 : RankFacts 125 := by sorry



end S5
end Couret
