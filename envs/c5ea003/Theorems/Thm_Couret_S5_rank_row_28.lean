-- Prove2me | Theorems.Thm_Couret_S5_rank_row_28
-- name    : Couret.S5.rank_row_28
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:44.65855+00:00
-- url     : https://prove2.me/theorems/46b542bf-3853-4680-88a2-bb260cac3635
-- title:
--   Subproduct rank certificate at mask 28
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=28$,
--
--   $$r(28)\le5,\qquad r(28)=5\Longleftrightarrow 1\text{ belongs to mask }28,\qquad \min(r(28)+1,5)\le r(\sigma(28,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock01.lean, lines 19–19; source file SHA-256 e38be7835ee0f83719ae9bf298fb52efab4af74644d76cd11fb094e838048212; theorem Couret.S5.rank_row_28

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_28 : RankFacts 28 := by sorry




end S5
end Couret
