-- Prove2me | Theorems.Thm_Couret_S5_rank_row_71
-- name    : Couret.S5.rank_row_71
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:11.345172+00:00
-- url     : https://prove2.me/theorems/99970d1d-44df-43d0-a4be-1200b9ca0157
-- title:
--   Subproduct rank certificate at mask 71
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=71$,
--
--   $$r(71)\le5,\qquad r(71)=5\Longleftrightarrow 1\text{ belongs to mask }71,\qquad \min(r(71)+1,5)\le r(\sigma(71,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock04.lean, lines 14–14; source file SHA-256 68222c858830a0c00cda6c41384eaefb0092251c70b6430ca331c5231337e785; theorem Couret.S5.rank_row_71

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_71 : RankFacts 71 := by sorry









end S5
end Couret
