-- Prove2me | Theorems.Thm_Couret_S5_rank_row_8
-- name    : Couret.S5.rank_row_8
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:22.623171+00:00
-- url     : https://prove2.me/theorems/808b7805-8c6a-4dd0-a153-adbed37b0a90
-- title:
--   Subproduct rank certificate at mask 8
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=8$,
--
--   $$r(8)\le5,\qquad r(8)=5\Longleftrightarrow 1\text{ belongs to mask }8,\qquad \min(r(8)+1,5)\le r(\sigma(8,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock00.lean, lines 15–15; source file SHA-256 5b5b79d47dbea03302241f73ec335797269838fe2f41d74a323693005f369d9b; theorem Couret.S5.rank_row_8

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_8 : RankFacts 8 := by sorry








end S5
end Couret
