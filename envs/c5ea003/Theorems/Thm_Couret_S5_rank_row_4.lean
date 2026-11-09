-- Prove2me | Theorems.Thm_Couret_S5_rank_row_4
-- name    : Couret.S5.rank_row_4
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:14:22.043942+00:00
-- url     : https://prove2.me/theorems/460de9ae-71c5-451b-99c6-697d133a4e6f
-- title:
--   Rank certificate for mask 4
-- statement:
--   Let $r(m)$ be the specified rank table for the mask of unit residues modulo 30, and let $s_g(m)$ be the specified subproduct-mask update by a residue code $g\in C_2\times C_4$. For the fixed mask $m=4$,
--
--   $$r(m)\le5,\qquad r(m)=5\iff (0,0)\in\operatorname{supp}(m),\qquad \forall g,\ \min(r(m)+1,5)\le r(s_g(m)).$$
--
--   Here mask support uses the eight-bit residue ordering $1,7,11,13,17,19,23,29$, and $(0,0)$ is the code of residue one. This is one finite certificate row; no assertion for other masks is made by this row alone.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock00.lean, lines 11–11; source file SHA-256 5b5b79d47dbea03302241f73ec335797269838fe2f41d74a323693005f369d9b; theorem Couret.S5.rank_row_4

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankData_b110b8255ff4
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_4 : RankFacts 4 := by sorry












end S5
end Couret
