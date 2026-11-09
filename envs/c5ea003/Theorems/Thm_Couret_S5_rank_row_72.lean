-- Prove2me | Theorems.Thm_Couret_S5_rank_row_72
-- name    : Couret.S5.rank_row_72
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:10.261276+00:00
-- url     : https://prove2.me/theorems/941e061f-11ef-4cff-adb0-376b8f970227
-- title:
--   Rank certificate for mask 72
-- statement:
--   Let $r(m)$ be the specified rank table for the mask of unit residues modulo 30, and let $s_g(m)$ be the specified subproduct-mask update by a residue code $g\in C_2\times C_4$. For the fixed mask $m=72$,
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in\operatorname{supp}(m),\qquad \forall g,\ \min(r(m)+1,5)\le r(s_g(m)).$$
--
--   Here mask support uses the eight-bit residue ordering $1,7,11,13,17,19,23,29$, and $(0,0)$ is the code of residue one. This is one finite certificate row; no assertion for other masks is made by this row alone.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock04.lean, lines 15–15; source file SHA-256 68222c858830a0c00cda6c41384eaefb0092251c70b6430ca331c5231337e785; theorem Couret.S5.rank_row_72

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_72 : RankFacts 72 := by sorry








end S5
end Couret
