-- Prove2me | Theorems.Thm_Couret_S5_rank_row_214
-- name    : Couret.S5.rank_row_214
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:12:25.962728+00:00
-- url     : https://prove2.me/theorems/70df2c26-1e7c-4358-bfe0-b3ba76bc8cdf
-- title:
--   Subproduct rank certificate at mask 214
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=214$,
--
--   $$r(214)\le5,\qquad r(214)=5\Longleftrightarrow 1\text{ belongs to mask }214,\qquad \min(r(214)+1,5)\le r(\sigma(214,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock13.lean, lines 13–13; source file SHA-256 459ec068eceb18493966b260925716bbfcf7ed2d8dc30afa4c14f69b504a59fe; theorem Couret.S5.rank_row_214

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_214 : RankFacts 214 := by sorry










end S5
end Couret
