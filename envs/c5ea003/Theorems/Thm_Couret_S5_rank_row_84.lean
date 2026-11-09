-- Prove2me | Theorems.Thm_Couret_S5_rank_row_84
-- name    : Couret.S5.rank_row_84
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:34.980067+00:00
-- url     : https://prove2.me/theorems/cc4a6131-13a0-426b-9a0f-d81ae346d3e8
-- title:
--   Subproduct rank certificate for mask 84
-- statement:
--   Let $m=84$ be the fixed subproduct mask, let $r(m)$ be its tabulated rank, and let $S(m)$ be its support in the residue-code group $C_2\times C_4$, with identity $(0,0)$. For every residue code $g$, write $T_g(m)$ for the mask after adjoining that code. Then
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in S(m),\qquad \min(r(m)+1,5)\le r(T_g(m)).$$
--
--   The last assertion includes every code $g$ without restrictions. This certificate provides one row of the finite rank argument for the five-factor threshold.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock05.lean, lines 11–11; source file SHA-256 e78c60f253ce4867d6acb20b04f8a6585259ff94a4208908bde16cbe68fcd5c7; theorem Couret.S5.rank_row_84

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_84 : RankFacts 84 := by sorry












end S5
end Couret
