-- Prove2me | solution 1 for mme_more_asymmetry_released_boundary_word_grade_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T19:04:31.69703+00:00
-- url     : https://prove2.me/submissions/c382cb83-c567-44eb-9510-1649dad5205b

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed

open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem solution :
    ∀ t ∈ terms, t.boundary ≠ [] →
      ∀ b ∈ t.boundary,
        (if t.shape.getD 0 0 = 0 then
          b.1.sum = t.shape.getD 1 0
        else
          b.1.sum = t.shape.getD 0 0) := by
  decide
