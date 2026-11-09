-- Prove2me | Theorems.Thm_Couret_S5_rank_row_141
-- name    : Couret.S5.rank_row_141
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:05.808423+00:00
-- url     : https://prove2.me/theorems/d563325f-4202-403d-a717-983e5692f990
-- title:
--   Subproduct rank certificate at mask 141
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=141$,
--
--   $$r(141)\le5,\qquad r(141)=5\Longleftrightarrow 1\text{ belongs to mask }141,\qquad \min(r(141)+1,5)\le r(\sigma(141,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock08.lean, lines 20–20; source file SHA-256 c09065767e9eab364ed3ea86037ad1e4b4f8918703497076bdc84e76bbb0bd0d; theorem Couret.S5.rank_row_141

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_141 : RankFacts 141 := by sorry



end S5
end Couret
