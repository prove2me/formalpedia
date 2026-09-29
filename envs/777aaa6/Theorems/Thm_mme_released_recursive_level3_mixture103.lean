-- Prove2me | Theorems.Thm_mme_released_recursive_level3_mixture103
-- name    : mme_released_recursive_level3_mixture103
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T11:33:49.442177+00:00
-- url     : https://prove2.me/theorems/64c46be1-fc2e-443b-82a5-fa5901ea0bef
-- title:
--   Mixture entropy floors for regions 87 to 87 of level-three band 3
-- statement:
--   A rational lower bound on the mixture entropy of 1 region-and-mode pairs of
--   level-three band 3, covering regions 87 to 87.
--
--   The mixture distribution of a region spreads over pairs of parent words. The bound is the floor a
--   table of small-prime references assigns to that distribution, corrected by certified logarithm
--   enclosures, and it is stated only over the word pairs the distribution actually charges.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
import Theorems.Thm_mme_certified_floor_support
import Theorems.Thm_mme_certified_mixture_support
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level3_mixture103 :
    ((1765877064863975176973636522946 : ℚ)/10^30 ≤
      regFloorG (mixQ (htotal3 3) (n3 3) (m3 3) (mu3 3 2) (87 : Fin 88))
        (fun (w : (Fin 2 → CompleteSplit.CompleteWord 2)) (k : Fin 4) => if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 26 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 44 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 50 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 52 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 62 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 68 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 70 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 74 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 76 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if (3 * (w 0 0).val + (w 0 1).val) * 9 + (3 * (w 1 0).val + (w 1 1).val) = 78 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) := by sorry
