-- Prove2me | solution 1 for mme_more_asymmetry_released_boundary_shapes_have_zero_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T19:17:02.99316+00:00
-- url     : https://prove2.me/submissions/55c08a58-535c-49ce-85c8-f4915d5c6908

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed

open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem solution :
    ∀ i : Fin terms.length, (terms[i]).boundary ≠ [] →
      (terms[i]).shape.getD 0 0 = 0 ∨
      (terms[i]).shape.getD 1 0 = 0 ∨
      (terms[i]).shape.getD 2 0 = 0 := by
  decide
