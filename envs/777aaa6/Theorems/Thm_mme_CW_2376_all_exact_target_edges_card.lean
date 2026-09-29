-- Prove2me | Theorems.Thm_mme_CW_2376_all_exact_target_edges_card
-- name    : mme_CW_2376_all_exact_target_edges_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:51:30.76575+00:00
-- url     : https://prove2.me/theorems/0486fe83-9913-4ac6-b79c-6d9bb3282240
-- title:
--   The exact target subset is equinumerous with exact-profile addresses
-- statement:
--   The complete exact-target subset of the full marginal-supported Coppersmith--Winograd hypergraph is canonically in bijection with the original type of exact-profile addresses. Consequently their cardinalities agree.
--
--   The nontrivial direction uses the already proved facts that every exact-profile address is coordinatewise supported and has the prescribed five-grade marginal in all three modes. Thus embedding the target into the larger ambient hypergraph introduces no new target edges and loses none.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) and the full marginal pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_exact_profile_address_supported
import Theorems.Thm_mme_CW_2376_exact_profile_address_marginals

open MME

set_option autoImplicit false

theorem mme_CW_2376_all_exact_target_edges_card
    (m : ℕ) :
    (cw2376AllExactTargetEdges m).card =
      Nat.card (CW2376ExactProfileAddress m) := by
  sorry
