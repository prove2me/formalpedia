-- Prove2me | Theorems.Thm_Couret_S5_rank_row_25
-- name    : Couret.S5.rank_row_25
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:37.080005+00:00
-- url     : https://prove2.me/theorems/be075687-a188-4473-bea8-ab21f34ed55a
-- title:
--   Subproduct rank certificate at mask 25
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=25$,
--
--   $$r(25)\le5,\qquad r(25)=5\Longleftrightarrow 1\text{ belongs to mask }25,\qquad \min(r(25)+1,5)\le r(\sigma(25,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock01.lean, lines 16–16; source file SHA-256 e38be7835ee0f83719ae9bf298fb52efab4af74644d76cd11fb094e838048212; theorem Couret.S5.rank_row_25

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_25 : RankFacts 25 := by sorry







end S5
end Couret
