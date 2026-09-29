-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_boundary_shapes_have_zero_coordinate
-- name    : mme_more_asymmetry_released_boundary_shapes_have_zero_coordinate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T19:16:05.258471+00:00
-- url     : https://prove2.me/theorems/b5428b00-5032-49ec-b3e5-cab3c910a5f7
-- title:
--   Released boundary terms have a zero parent coordinate
-- statement:
--   For each index in the concatenated six-owner released exact-profile table, if its term has a nonempty boundary four-word profile, then at least one coordinate of the parent shape is zero. This is the shape-side support condition needed to transport the canonical boundary split construction to each of the three zero-coordinate orientations.
-- source:
--   Literal finite data in MME.MoreAsymmetryExactSeed.terms from the pinned v2 exact-profile seed definition, SHA-256 e86521ba2d2640841f44e4876b55a26c18b055cfc6e59ebf2cf9f3f70932fa28. The fact is checked by exact table audit and formalized as a closed finite-index proposition.

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem mme_more_asymmetry_released_boundary_shapes_have_zero_coordinate :
    ∀ i : Fin terms.length, (terms[i]).boundary ≠ [] →
      (terms[i]).shape.getD 0 0 = 0 ∨
      (terms[i]).shape.getD 1 0 = 0 ∨
      (terms[i]).shape.getD 2 0 = 0 := by sorry
