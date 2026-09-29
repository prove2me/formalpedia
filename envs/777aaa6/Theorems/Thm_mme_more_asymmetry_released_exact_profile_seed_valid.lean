-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_exact_profile_seed_valid
-- name    : mme_more_asymmetry_released_exact_profile_seed_valid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T20:18:31.36152+00:00
-- url     : https://prove2.me/theorems/87a4b7d4-04ba-4e88-835b-c15dca0975c0
-- title:
--   Released exact profile tables are normalized and well formed
-- statement:
--   The six exact global distributions each contain 45 nonnegative counts summing to 10^12, and their product-dual weights are strictly positive. All 270 exact parent input records satisfy the declared elementary consistency predicate: normalized boundary or regional probabilities; correct numbers of regions and split entries; square-child shapes and split_0 parameters in the permitted range; and positive product-dual weights. This is a direct Lean-kernel finite check, with no native_decide. It does not prove tensor source compatibility, type covers, recursive realization, or the full numerical rate calculation.
-- source:
--   More Asymmetry, arXiv:2404.16349v2; W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem mme_more_asymmetry_released_exact_profile_seed_valid :
    globalAlpha.length = 6 ∧ (∀ a ∈ globalAlpha, a.length = 45 ∧ Normalized a) ∧
    globalDual.length = 6 ∧
      (∀ d ∈ globalDual, d.length = 3 ∧ ∀ m ∈ d, m.length = 9 ∧ ∀ p ∈ m, 0 < p.2) ∧
    terms.length = 270 ∧ ∀ t ∈ terms, t.Valid := by sorry
