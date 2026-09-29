-- Prove2me | Theorems.Thm_mme_released_recursive_stage_level2_rate
-- name    : mme_released_recursive_stage_level2_rate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-22T18:22:45.343844+00:00
-- url     : https://prove2.me/theorems/74983532-d405-439d-ae5f-67edb59b670a
-- title:
--   Pooled level-2 recursive stage data: regional rate
-- statement:
--   The regional rate of the pooled level-2 region of the released recursive data is more than `585967770317 * 6 * 10^48`, that is, more than `0.585967770317` per global block.
--
--   The pooled region has 1104 positive level-2 terms. Its level-1 halves carry their own grade as their word, so the compatibility potential vanishes and each of the three mode rates is a weighted sum of split entropies: `log 2` for a mode whose grade is one, and the entropy of `(s, s, 1 - 2s)` for the mode whose grade is two, where `s` is the term's split parameter.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6, applied to the published exact seed of the released parameters. Numerical statement about the published data; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_regional_split_entropy_data
open BigOperators MME MME.RecursiveYZ MME.RegionRate MME.RecStage
set_option autoImplicit false

theorem mme_released_recursive_stage_level2_rate :
    ((585967770317 * 6 * 10 ^ 48 : ℕ) : ℝ) < regionalRate htotal2 n2 m2 mu2 := by sorry
