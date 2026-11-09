-- Prove2me | Theorems.Thm_Couret_S5_full_T_at_identity
-- name    : Couret.S5.full_T_at_identity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:33.047467+00:00
-- url     : https://prove2.me/theorems/fe3fc2c1-c766-4b29-9686-fd5bc7265c48
-- title:
--   Six pairs at the full identity mask
-- statement:
--   The pair list for total residue code $(0,0)$ and mask 255 has length exactly six: $$|L((0,0),255)|=6.$$
--
--   This concerns list length, retaining the implementation ordering.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/OptimalFive.lean, lines 84–84; source file SHA-256 10e4872f2ae446d57ad6e2c526d92085da7cdb70df9bb99e2641c0da1b7e7c1f; theorem Couret.S5.full_T_at_identity

import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
import Std
import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem full_T_at_identity : (pairList (0,0) 255).length = 6 := by sorry


end S5
end Couret
