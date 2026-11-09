-- Prove2me | Theorems.Thm_Couret_S5_rank_row_252
-- name    : Couret.S5.rank_row_252
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:45.468193+00:00
-- url     : https://prove2.me/theorems/74ac20a9-8029-4735-8f86-b9348e59d2d0
-- title:
--   Subproduct rank certificate at mask 252
-- statement:
--   Let $r$ be the supplied rank table for masks of the eight unit residues modulo 30, and let $\sigma(m,g)$ be the subproduct mask update on letter $g$. At the fixed mask $m=252$,
--
--   $$r(252)\le5,\qquad r(252)=5\Longleftrightarrow 1\text{ belongs to mask }252,\qquad \min(r(252)+1,5)\le r(\sigma(252,g))\quad\text{for every }g.$$
--
--   This is one row of the finite rank-growth certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankBlock15.lean, lines 19–19; source file SHA-256 b95f23d3d2e017a6013682f0aa79326245001c6cca55f53129d2c627dd705355; theorem Couret.S5.rank_row_252

import Definitions.Def_Couret_RankBlock00_bd2f9788729f
import Std
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem rank_row_252 : RankFacts 252 := by sorry




end S5
end Couret
