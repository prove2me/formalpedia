-- Prove2me | Theorems.Thm_Couret_S5_rank_row_130
-- name    : Couret.S5.rank_row_130
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:09:01.031622+00:00
-- url     : https://prove2.me/theorems/7262a153-8997-4fab-babc-84a01fd45fae
-- title:
--   Subproduct rank certificate at mask 130
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=130$,
--
--   $$r(130)\le5,\qquad r(130)=5\Longleftrightarrow 1\text{ belongs to mask }130,\qquad \min(r(130)+1,5)\le r(\sigma(130,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock08.lean, lines 9–9; source file SHA-256 c09065767e9eab364ed3ea86037ad1e4b4f8918703497076bdc84e76bbb0bd0d; theorem Couret.S5.rank_row_130

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_130 : RankFacts 130 := by sorry














end S5
end Couret
