-- Prove2me | solution 1 for mme_more_asymmetry_released_exact_profile_seed_valid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T20:19:57.686565+00:00
-- url     : https://prove2.me/submissions/474ca07b-a353-48c2-ab04-bdfddf3d0361

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem solution :
    globalAlpha.length = 6 ∧ (∀ a ∈ globalAlpha, a.length = 45 ∧ Normalized a) ∧
    globalDual.length = 6 ∧
      (∀ d ∈ globalDual, d.length = 3 ∧ ∀ m ∈ d, m.length = 9 ∧ ∀ p ∈ m, 0 < p.2) ∧
    terms.length = 270 ∧ ∀ t ∈ terms, t.Valid := by
  decide +kernel
