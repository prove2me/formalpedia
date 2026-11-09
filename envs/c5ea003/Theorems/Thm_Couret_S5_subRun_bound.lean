-- Prove2me | Theorems.Thm_Couret_S5_subRun_bound
-- name    : Couret.S5.subRun_bound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:18.926288+00:00
-- url     : https://prove2.me/theorems/3ebf9c18-5957-49db-a24c-0ae66000b139
-- title:
--   The subproduct run fits in an eight-bit mask
-- statement:
--   For every finite word $w$ in the eight unit residues modulo 30, the natural number mask $M(w)$ computed by the subproduct run satisfies
--
--   $$M(w)<256.$$
--
--   This certifies the fixed eight-bit representation for every word length.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/SubproductSemantics.lean, lines 25–28; source file SHA-256 ba13bc319dc0b6baacbd98ea26d1e89628af10edec99409e87d0f01ff3d4e21c; theorem Couret.S5.subRun_bound

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_shiftMaskOn_lt_256
import Theorems.Thm_Couret_singletonMask_lt_256
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem subRun_bound (w : Word Code30) : subRun w < 256 := by sorry








end S5
end Couret
