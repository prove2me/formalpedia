-- Prove2me | Theorems.Thm_Couret_S5_rank_row_16
-- name    : Couret.S5.rank_row_16
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:34.731068+00:00
-- url     : https://prove2.me/theorems/115e0c63-8b78-4c01-a2ef-d869c7fd63ba
-- title:
--   Subproduct rank certificate for mask 16
-- statement:
--   Let $m=16$ be the fixed subproduct mask, let $r(m)$ be its tabulated rank, and let $S(m)$ be its support in the residue-code group $C_2\times C_4$, with identity $(0,0)$. For every residue code $g$, write $T_g(m)$ for the mask after adjoining that code. Then
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in S(m),\qquad \min(r(m)+1,5)\le r(T_g(m)).$$
--
--   The last assertion includes every code $g$ without restrictions. This certificate provides one row of the finite rank argument for the five-factor threshold.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock01.lean, lines 7–7; source file SHA-256 e38be7835ee0f83719ae9bf298fb52efab4af74644d76cd11fb094e838048212; theorem Couret.S5.rank_row_16

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_16 : RankFacts 16 := by sorry
















end S5
end Couret
