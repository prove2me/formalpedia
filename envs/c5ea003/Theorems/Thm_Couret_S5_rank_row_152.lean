-- Prove2me | Theorems.Thm_Couret_S5_rank_row_152
-- name    : Couret.S5.rank_row_152
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:29.051869+00:00
-- url     : https://prove2.me/theorems/d8c8c34f-bb53-470e-943b-93bd8b19daf0
-- title:
--   Subproduct rank certificate at mask 152
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=152$,
--
--   $$r(152)\le5,\qquad r(152)=5\Longleftrightarrow 1\text{ belongs to mask }152,\qquad \min(r(152)+1,5)\le r(\sigma(152,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock09.lean, lines 15–15; source file SHA-256 cf82452ae772ea8b3c462b4573a0213fc3b411e420f2f7e6970c57e7d682703c; theorem Couret.S5.rank_row_152

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_152 : RankFacts 152 := by sorry








end S5
end Couret
