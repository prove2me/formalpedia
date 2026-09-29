-- Prove2me | Theorems.Thm_mme_regional_sparse_conditional_entropy
-- name    : mme_regional_sparse_conditional_entropy
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:33:25.732854+00:00
-- url     : https://prove2.me/theorems/c1bb0db7-0472-47b1-b768-a9601861be1d
-- title:
--   Exact conditional entropy for deterministically graded parent words
-- statement:
--   When a joint word has at most one possible coarse grade, the sum of the grade-conditioned mass entropies equals joint-word mass entropy minus coarse-grade mass entropy. The joint word is not replaced by separate child marginals.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign. Supporting result for https://arxiv.org/html/2404.16349v2#S6 . This result alone is not the regional extraction theorem or a numerical omega certificate.

import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_region_count_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_regional_sparse_conditional_entropy {J W : Type*} [Fintype J] [Fintype W] (x : J → W → ℝ)
    (hsparse : ∀ w j k, x j w ≠ 0 → x k w ≠ 0 → j = k) :
    (∑ j, massEntropy (x j)) =
      massEntropy (fun w ↦ ∑ j, x j w) - massEntropy (fun j ↦ ∑ w, x j w) := by sorry
