-- Prove2me | Theorems.Thm_Couret_S5_rank_row_171
-- name    : Couret.S5.rank_row_171
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:55.706791+00:00
-- url     : https://prove2.me/theorems/f41fecdc-d604-44eb-9082-09e22a7b8154
-- title:
--   Subproduct rank certificate at mask 171
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=171$,
--
--   $$r(171)\le5,\qquad r(171)=5\Longleftrightarrow 1\text{ belongs to mask }171,\qquad \min(r(171)+1,5)\le r(\sigma(171,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock10.lean, lines 18–18; source file SHA-256 52b63cffad1c4846b6e501c6169d3b95ec6d20a23003c5390648bc639bbcb164; theorem Couret.S5.rank_row_171

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_171 : RankFacts 171 := by sorry





end S5
end Couret
