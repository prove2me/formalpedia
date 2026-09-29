-- Prove2me | Theorems.Thm_mme_released_recursive_stage_region4_rate_margin
-- name    : mme_released_recursive_stage_region4_rate_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T22:58:19.239034+00:00
-- url     : https://prove2.me/theorems/e1adcbfb-285d-4292-8c5d-5d6b874fb6bd
-- title:
--   Regional rate lower bound for region 4, with margin
-- statement:
--   A lower bound on the regional entropy rate of region 4 of the released recursive stage.
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

theorem mme_released_recursive_stage_region4_rate_margin :
    ((123252768423 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 4) (n3 4) (m3 4) (mu3 4) := by sorry
