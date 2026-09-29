-- Prove2me | Theorems.Thm_mme_regional_coarse_entropy_bound
-- name    : mme_regional_coarse_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T21:16:37.580335+00:00
-- url     : https://prove2.me/theorems/5fc56455-6fa5-4e58-92a1-4a0c1d1e5ce2
-- title:
--   The physical mode entropy is at most joint split entropy
-- statement:
--   Apply finite entropy coarsening to the actual physical split marginals and sum over the entire region.
-- source:
--   The More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Uniform bounds for the actual common hash construction; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_regional_coarse_entropy_bound {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    coarsePotential m i ≤ jointPotential m := by sorry
