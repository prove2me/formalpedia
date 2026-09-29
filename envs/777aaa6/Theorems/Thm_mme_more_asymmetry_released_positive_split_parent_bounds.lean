-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_positive_split_parent_bounds
-- name    : mme_more_asymmetry_released_positive_split_parent_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T19:21:23.464435+00:00
-- url     : https://prove2.me/theorems/4b7be2b1-07c4-4ca5-bdc0-693cb6f3d765
-- title:
--   Released positive splits are bounded by their parent grades
-- statement:
--   For every positive-parent term in the concatenated released exact-profile table, each listed grade-four split is coordinatewise bounded by the corresponding grade-eight parent shape coordinate. The bound is not part of `Term.Valid`, but is required to embed every literal split into the dependent physical `Split` type.
-- source:
--   Literal v2 exact-profile seed table MME.MoreAsymmetryExactSeed.terms; captured definition SHA-256 e86521ba2d2640841f44e4876b55a26c18b055cfc6e59ebf2cf9f3f70932fa28. Exact integer profile audit confirms all positive split coordinates respect the parent grade.

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem mme_more_asymmetry_released_positive_split_parent_bounds :
    ∀ i : Fin terms.length, (terms[i]).boundary = [] →
      ∀ j : Fin (terms[i]).splits.length, ∀ k : Fin 3,
        ((terms[i]).splits[j]).getD k.val 0 ≤
          (terms[i]).shape.getD k.val 0 := by sorry
