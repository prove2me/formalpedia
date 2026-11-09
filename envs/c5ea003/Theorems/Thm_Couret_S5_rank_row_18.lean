-- Prove2me | Theorems.Thm_Couret_S5_rank_row_18
-- name    : Couret.S5.rank_row_18
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:11:36.191474+00:00
-- url     : https://prove2.me/theorems/c63a9162-b034-45c2-bb5c-f004e323c2f8
-- title:
--   Subproduct rank certificate at mask 18
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=18$,
--
--   $$r(18)\le5,\qquad r(18)=5\Longleftrightarrow 1\text{ belongs to mask }18,\qquad \min(r(18)+1,5)\le r(\sigma(18,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock01.lean, lines 9–9; source file SHA-256 e38be7835ee0f83719ae9bf298fb52efab4af74644d76cd11fb094e838048212; theorem Couret.S5.rank_row_18

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_18 : RankFacts 18 := by sorry














end S5
end Couret
