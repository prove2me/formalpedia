-- Prove2me | Theorems.Thm_Couret_S5_rank_row_225
-- name    : Couret.S5.rank_row_225
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:09.569499+00:00
-- url     : https://prove2.me/theorems/2945dea6-c36a-41b2-ae28-509267ab69a9
-- title:
--   Subproduct rank certificate at mask 225
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=225$,
--
--   $$r(225)\le5,\qquad r(225)=5\Longleftrightarrow 1\text{ belongs to mask }225,\qquad \min(r(225)+1,5)\le r(\sigma(225,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock14.lean, lines 8–8; source file SHA-256 efccd07f7a77ca64ab872bb12ccb4e9bc4540b9e7a3012eef771d5e4531f0e30; theorem Couret.S5.rank_row_225

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_225 : RankFacts 225 := by sorry















end S5
end Couret
