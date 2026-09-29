-- Prove2me | solution 1 for mme_more_asymmetry_released_positive_split_parent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T19:22:07.051505+00:00
-- url     : https://prove2.me/submissions/4a0d7cab-8555-471c-9857-abe2eeb92f78

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed

open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem solution :
    ∀ i : Fin terms.length, (terms[i]).boundary = [] →
      ∀ j : Fin (terms[i]).splits.length, ∀ k : Fin 3,
        ((terms[i]).splits[j]).getD k.val 0 ≤
          (terms[i]).shape.getD k.val 0 := by
  decide
