-- Prove2me | Theorems.Thm_Couret_S5_rank_row_215
-- name    : Couret.S5.rank_row_215
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:12:28.496867+00:00
-- url     : https://prove2.me/theorems/c6f55e57-31d5-4250-bd6c-20a6bbcfd18c
-- title:
--   Rank certificate for mask 215
-- statement:
--   Let $r(m)$ be the specified rank table for the mask of unit residues modulo 30, and let $s_g(m)$ be the specified subproduct-mask update by a residue code $g\in C_2\times C_4$. For the fixed mask $m=215$,
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in\operatorname{supp}(m),\qquad \forall g,\ \min(r(m)+1,5)\le r(s_g(m)).$$
--
--   Here mask support uses the eight-bit residue ordering $1,7,11,13,17,19,23,29$, and $(0,0)$ is the code of residue one. This is one finite certificate row; no assertion for other masks is made by this row alone.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock13.lean, lines 14–14; source file SHA-256 459ec068eceb18493966b260925716bbfcf7ed2d8dc30afa4c14f69b504a59fe; theorem Couret.S5.rank_row_215

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_215 : RankFacts 215 := by sorry









end S5
end Couret
