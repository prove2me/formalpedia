-- Prove2me | Theorems.Thm_mme_regional_entropy_penalty_bound
-- name    : mme_regional_entropy_penalty_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:42.444016+00:00
-- url     : https://prove2.me/theorems/98b64bdb-84eb-43ae-b342-b0816d0d6ac8
-- title:
--   The existing entropy penalty bounds all same-marginal distributions
-- statement:
--   Prove finiteness of the existing entropy supremum on the finite probability cube, nonnegativity of its penalty, and the natural-log entropy comparison for every distribution with the same physical marginals.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem mme_regional_entropy_penalty_bound {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (hpos : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    0 ≤ entropyPenalty alpha ∧
    ∀ rho ∈ SameMarginalDistributions alpha,
      entropy rho ≤ entropy alpha + Real.log 2 * entropyPenalty alpha := by sorry
