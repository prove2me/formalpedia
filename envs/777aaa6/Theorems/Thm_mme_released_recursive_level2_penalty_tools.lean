-- Prove2me | Theorems.Thm_mme_released_recursive_level2_penalty_tools
-- name    : mme_released_recursive_level2_penalty_tools
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T02:17:41.933365+00:00
-- url     : https://prove2.me/theorems/dbda71ed-703e-4f68-8eb9-8cff6cc0a70a
-- title:
--   Tools for certifying the level-two penalty region by region
-- statement:
--   The tools needed to certify a level-two penalty region by region.
--
--   The normalized split weights are nonnegative, sum to one, and are the small split weight over the
--   scale. Only the parametric coordinate contributes to the penalty reference, so the sum over the
--   three coordinates collapses. A sum over grade triples is an explicit threefold sum. For each of the
--   three parent shapes, the four split weights are given in closed form in the region's weight
--   parameter. And the penalty of a region is bounded by the purely rational expression built from its
--   references.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_potential_floor
import Theorems.Thm_mme_released_recursive_stage_level2_counts0
import Theorems.Thm_mme_released_recursive_stage_level2_counts1
import Theorems.Thm_mme_released_recursive_stage_level2_counts2
import Theorems.Thm_mme_released_recursive_stage_level2_counts3
import Theorems.Thm_mme_certified_entropy_penalty_rational

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_penalty_tools :
    (∀ (r : Fin 1104) (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)),
      0 ≤ alphaQ r c ∧ alphaQ r c = (jwv r c.val : ℚ) / (D : ℚ)) ∧
    (∀ r : Fin 1104, ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      alphaQ r c = 1) ∧
    (∀ (r : Fin 1104) (a : Tri) (k : Fin 4),
      ∑ i, PE r i (a i) k = PE r (certMode r) (a (certMode r)) k) ∧
    (∀ g : Tri → ℚ, ∑ a : Tri, g a =
      ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z]) ∧
    (∀ (r : Fin 1104), parent2 r = ![1, 1, 2] →
      jwv r ![0, 0, 2] = (l2At r).2.2 ∧ jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![1, 1, 0] = (l2At r).2.2) ∧
    (∀ (r : Fin 1104), parent2 r = ![1, 2, 1] →
      jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![0, 2, 0] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = (l2At r).2.2 ∧ jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2) ∧
    (∀ (r : Fin 1104), parent2 r = ![2, 1, 1] →
      jwv r ![0, 1, 1] = (l2At r).2.2 ∧ jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 ∧ jwv r ![2, 0, 0] = (l2At r).2.2) ∧
    ∀ r : Fin 1104,
      Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)) ≤
        (((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
            qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
          ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
            (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t) : ℚ) : ℝ) := by sorry
