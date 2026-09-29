-- Prove2me | Theorems.Thm_mme_released_global_x_data_valid
-- name    : mme_released_global_x_data_valid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:57:07.578639+00:00
-- url     : https://prove2.me/theorems/ab5bcb81-e052-4052-9067-a1caaa17f00b
-- title:
--   Exact rational data for the six released global X-rate certificates
-- statement:
--   Validate the rational coarse masses, marginals, normalized positive dual distributions, all 594 logarithm inputs, and the six rational arithmetic floor inequalities for the exact released global candidate.
-- source:
--   Numerical global X-rate certification for the exact ReleasedGlobal candidate from More Asymmetry, https://arxiv.org/html/2404.16349v2#S5 . Y/Z numerical rates and whole-interface recursive continuation remain separate.

import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000

theorem mme_released_global_x_data_valid :
    (∀ o s, 0 ≤ alphaQ o s) ∧
    (∀ o, ∑ s, alphaQ o s = 1) ∧
    (∀ o i, ∑ j, marginalQ o i j = 1) ∧
    (∀ o i j, 0 < dualCounts o i j) ∧
    (∀ o, 0 < dualTotal o) ∧
    (∀ o, ∑ s, dualQ o s = 1) ∧
    (∀ o s, 0 < dualQ o s) ∧
    (∀ o j, 0 ≤ marginalQ o 0 j) ∧
    (∀ o s, xInputs o ⟨s.val,by omega⟩ = alphaQ o s) ∧
    (∀ o s, xInputs o ⟨45+s.val,by omega⟩ = dualQ o s) ∧
    (∀ o j, xInputs o ⟨90+j.val,by omega⟩ = marginalQ o 0 j) ∧
    (∀ o, rateFloor o ≤ xBound o) := by
  sorry
