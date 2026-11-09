-- Prove2me | Theorems.Thm_Couret_S5_rank_row_9
-- name    : Couret.S5.rank_row_9
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:42.031637+00:00
-- url     : https://prove2.me/theorems/fa1cc781-1a54-435e-9d67-c0e1ba0e6529
-- title:
--   Subproduct rank certificate for mask 9
-- statement:
--   Let $m=9$ be the fixed subproduct mask, let $r(m)$ be its tabulated rank, and let $S(m)$ be its support in the residue-code group $C_2\times C_4$, with identity $(0,0)$. For every residue code $g$, write $T_g(m)$ for the mask after adjoining that code. Then
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in S(m),\qquad \min(r(m)+1,5)\le r(T_g(m)).$$
--
--   The last assertion includes every code $g$ without restrictions. This certificate provides one row of the finite rank argument for the five-factor threshold.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock00.lean, lines 16–16; source file SHA-256 5b5b79d47dbea03302241f73ec335797269838fe2f41d74a323693005f369d9b; theorem Couret.S5.rank_row_9

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_9 : RankFacts 9 := by sorry







end S5
end Couret
