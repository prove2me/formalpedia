-- Prove2me | Theorems.Thm_mme_released_recursive_stage_region3_rate
-- name    : mme_released_recursive_stage_region3_rate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-22T18:21:02.652079+00:00
-- url     : https://prove2.me/theorems/3a976154-bf64-4c3e-bd29-57e59f0b4d68
-- title:
--   Level-3 region 3 of the recursive stage data: regional rate
-- statement:
--   The regional rate of level-3 region 3 of the released recursive data is more than `122361313831 * 6 * 10^48`.
--
--   In the normalization where one unit of the global scale has `6 * 10^60` blocks, this says the region's rate is more than `0.122361313831` per block. The rate is the least of three quantities: the coarse split entropy minus the maximum-entropy penalty, and, for each of the two hashed modes, the parent-word entropy minus the compatibility potential of the cell partition.
--
--   The six regional rates and the pooled level-2 rate together have to reach the recursive rate `1.3223546` of the graded continuation; their exact values total about `1.32235555`, so the six regions and level 2 may lose at most about `10^-6` in total.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6, applied to the published exact seed of the released parameters. Numerical statement about the published data; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_regional_split_entropy_data
open BigOperators MME MME.RecursiveYZ MME.RegionRate MME.RecStage
set_option autoImplicit false

theorem mme_released_recursive_stage_region3_rate :
    ((122361313831 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 3) (n3 3) (m3 3) (mu3 3) := by sorry
