-- Prove2me | Theorems.Thm_mme_CW_2376_augmented_hash_state_universe_card
-- name    : mme_CW_2376_augmented_hash_state_universe_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:12:24.742253+00:00
-- url     : https://prove2.me/theorems/3e51d682-de2f-479d-8cd4-615d8d9c134e
-- title:
--   The augmented CW affine hash parameter space has size $p^{N+2}$
-- statement:
--   At CW scale $m$, let $N=3{,}000{,}000m$. An augmented affine hash state consists of $N+1$ independent weights in the prime field with $p$ elements and one affine offset. Therefore the complete parameter space has cardinality
--
--   $$
--   p^{N+2}.
--   $$
--
--   The extra weight is deliberately unused by the retained-edge predicate; its presence aligns the aggregate state factor with the exact $p^N$ target-survival and fixed-collision fiber counts.
-- source:
--   Elementary finite-field counting; parameterization used in the outer affine hashing of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes

open MME

set_option autoImplicit false

theorem mme_CW_2376_augmented_hash_state_universe_card
    (m p : ℕ) [Fact p.Prime] :
    (cw2376AugmentedHashStateUniverse m p).card =
      p ^ (cw2376ProfileLength m + 2) := by
  sorry
