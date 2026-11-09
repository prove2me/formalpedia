-- Prove2me | Theorems.Thm_Couret_S5_rank_row_165
-- name    : Couret.S5.rank_row_165
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:42.96936+00:00
-- url     : https://prove2.me/theorems/124d9000-b6a3-4f03-93fa-cd109d244bdf
-- title:
--   Subproduct rank certificate for mask 165
-- statement:
--   Let $m=165$ be the fixed subproduct mask, let $r(m)$ be its tabulated rank, and let $S(m)$ be its support in the residue-code group $C_2\times C_4$, with identity $(0,0)$. For every residue code $g$, write $T_g(m)$ for the mask after adjoining that code. Then
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in S(m),\qquad \min(r(m)+1,5)\le r(T_g(m)).$$
--
--   The last assertion includes every code $g$ without restrictions. This certificate provides one row of the finite rank argument for the five-factor threshold.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock10.lean, lines 12–12; source file SHA-256 52b63cffad1c4846b6e501c6169d3b95ec6d20a23003c5390648bc639bbcb164; theorem Couret.S5.rank_row_165

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_165 : RankFacts 165 := by sorry











end S5
end Couret
