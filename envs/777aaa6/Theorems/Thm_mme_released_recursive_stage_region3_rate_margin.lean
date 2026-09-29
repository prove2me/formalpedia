-- Prove2me | Theorems.Thm_mme_released_recursive_stage_region3_rate_margin
-- name    : mme_released_recursive_stage_region3_rate_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T22:57:39.647096+00:00
-- url     : https://prove2.me/theorems/cee956b4-e2d4-4c95-9e89-a345ac0a7f7d
-- title:
--   Regional rate lower bound for region 3, with margin
-- statement:
--   A lower bound on the regional entropy rate of region 3 of the released recursive stage.
--
--   The rate is the smallest of three potentials: the coarse potential of the split distribution minus
--   its maximum-entropy penalty, and, for each of the two non-leading modes, the parent potential of the
--   profile minus its compatibility potential. The constant is stated in the same units as the stage
--   data, namely a multiple of six times ten to the forty-eighth.
--
--   This is the same bound as the earlier statement for this region with a slightly smaller constant,
--   left with room to spare so that the certificate behind it can use a coarse reference grid.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_regional_split_entropy_data
open BigOperators MME MME.RecursiveYZ MME.RegionRate MME.RecStage
set_option autoImplicit false

theorem mme_released_recursive_stage_region3_rate_margin :
    ((122361213831 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 3) (n3 3) (m3 3) (mu3 3) := by sorry
