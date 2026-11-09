-- Prove2me | Theorems.Thm_Couret_S5_rank_row_90
-- name    : Couret.S5.rank_row_90
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:49.158858+00:00
-- url     : https://prove2.me/theorems/29047e39-f64e-4440-abff-e3994a38ca70
-- title:
--   Subproduct rank certificate at mask 90
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=90$,
--
--   $$r(90)\le5,\qquad r(90)=5\Longleftrightarrow 1\text{ belongs to mask }90,\qquad \min(r(90)+1,5)\le r(\sigma(90,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock05.lean, lines 17–17; source file SHA-256 e78c60f253ce4867d6acb20b04f8a6585259ff94a4208908bde16cbe68fcd5c7; theorem Couret.S5.rank_row_90

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_90 : RankFacts 90 := by sorry






end S5
end Couret
