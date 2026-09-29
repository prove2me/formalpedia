-- Prove2me | Theorems.Thm_mme_released_recursive_level2_structure
-- name    : mme_released_recursive_level2_structure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T20:38:40.240625+00:00
-- url     : https://prove2.me/theorems/19e141ef-762c-43d4-aa7c-2ec064994585
-- title:
--   Level two: vanishing compatibility potential and the mixture as a split marginal
-- statement:
--   Two structural facts about the level-two stage of the released recursive construction.
--
--   First, the compatibility potential of the level-two profile vanishes in both boundary roles. At
--   level two a half carries a single letter, so every part of the compatibility partition is
--   concentrated on one word and contributes no entropy. This means the level-two regional rate is the
--   plain parent potential, with nothing subtracted.
--
--   Second, the parent mixture of the level-two profile is the mode-`i` marginal of the split
--   distribution: the probability of a pair of one-letter words is the total weight of the splits whose
--   mode-`i` coordinate, and whose complement's mode-`i` coordinate, are the two letters.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_modern_entropy_data
open BigOperators MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.RecStage
open scoped Classical
set_option autoImplicit false

theorem mme_released_recursive_level2_structure :
    (∀ i : Fin 2, RegionRealization.potential
        (partCount (yzBoundary i) (modeGroup (yzMode i)) (mu2 (yzMode i))) = 0) ∧
    ∀ (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1),
      parentMixture htotal2 n2 m2 (mu2 i) r w =
        (∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          (if (w 0 0).val = (c.val i).val ∧
              (w 1 0).val = ((complement (htotal2 r) c).val i).val then (m2 r c : ℝ) else 0)) /
          (n2 r : ℝ) := by sorry
