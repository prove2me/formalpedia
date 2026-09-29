-- Prove2me | Theorems.Thm_mme_released_recursive_level2_coarse
-- name    : mme_released_recursive_level2_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T01:37:25.433248+00:00
-- url     : https://prove2.me/theorems/3c07af4e-3e0b-4fef-989f-2514b7bf53b5
-- title:
--   The level-two coarse potential equals the leading-mode parent potential
-- statement:
--   The level-two coarse potential is the same as the parent potential of the leading mode.
--
--   The parent mixture of a region is supported on pairs of a grade and its complement, so its entropy
--   is the entropy of the grade distribution alone. The coarse potential is built from the coordinate
--   marginals of the split distribution, which are the same grade counts up to the region's scale. So
--   the two potentials agree region by region, and the certified bound already proved for the parent
--   potential of the leading mode is also a bound for the coarse potential.
--
--   Also recorded: the closed form of those marginal counts, and that they total the region's size.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_potential_floor
import Theorems.Thm_mme_released_recursive_stage_level2_counts0
import Theorems.Thm_mme_released_recursive_stage_level2_counts1
import Theorems.Thm_mme_released_recursive_stage_level2_counts2
import Theorems.Thm_mme_released_recursive_stage_level2_counts3
import Theorems.Thm_mme_certified_entropy_bridge
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_coarse :
    (∀ (i : Fin 3) (r : Fin 1104), 0 < n2 r →
      entropy (fun w ↦ ((mixQ htotal2 n2 m2 (mu2 i) r w : ℚ) : ℝ)) =
        entropy (fun a : Fin 3 ↦ ((PG i r a : ℚ) : ℝ))) ∧
    (∀ (r : Fin 1104) (j : Fin 3),
      marginalCounts m2 0 r j = (l2At r).2.1 * Jm r 0 j * D) ∧
    (∀ r : Fin 1104, ∑ j, marginalCounts m2 0 r j = n2 r) ∧
    coarsePotential m2 0 = parentPotential htotal2 n2 m2 (mu2 0) := by sorry
