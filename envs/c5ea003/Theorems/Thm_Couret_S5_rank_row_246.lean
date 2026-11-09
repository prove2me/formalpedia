-- Prove2me | Theorems.Thm_Couret_S5_rank_row_246
-- name    : Couret.S5.rank_row_246
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:33.348836+00:00
-- url     : https://prove2.me/theorems/be6c70e7-8d01-4000-88bc-f68351475001
-- title:
--   Subproduct rank certificate for mask 246
-- statement:
--   Let $m=246$ be the fixed subproduct mask, let $r(m)$ be its tabulated rank, and let $S(m)$ be its support in the residue-code group $C_2\times C_4$, with identity $(0,0)$. For every residue code $g$, write $T_g(m)$ for the mask after adjoining that code. Then
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in S(m),\qquad \min(r(m)+1,5)\le r(T_g(m)).$$
--
--   The last assertion includes every code $g$ without restrictions. This certificate provides one row of the finite rank argument for the five-factor threshold.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock15.lean, lines 13–13; source file SHA-256 b95f23d3d2e017a6013682f0aa79326245001c6cca55f53129d2c627dd705355; theorem Couret.S5.rank_row_246

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_246 : RankFacts 246 := by sorry










end S5
end Couret
