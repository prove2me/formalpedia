-- Prove2me | Theorems.Thm_mme_CW_2376_collision_universe_card_of_degree
-- name    : mme_CW_2376_collision_universe_card_of_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:14:44.391248+00:00
-- url     : https://prove2.me/theorems/1d421dfa-783b-4ae2-91c9-66308ca80c8c
-- title:
--   Uniform completion degree bounds all target--ambient collisions by $3TD$
-- statement:
--   Let $T$ be the number of exact-profile target edges. Suppose that for every target edge and every one of the three modes, at most $D$ ambient marginal-supported edges share that mode word. Then the number of directed pairs from a target edge to a distinct ambient edge that share some mode is at most
--
--   $$
--   3TD.
--   $$
--
--   The estimate is a union bound over the three modes. Counting a pair more than once only strengthens the upper bound, so no uniqueness assumption on the shared mode is required here.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), collision deletion and uniform completion counts on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_2376_collision_universe_card_of_degree
    (m D : ℕ)
    (hdeg : ∀ i : Fin 3, ∀ a ∈ cw2376AllExactTargetEdges m,
      ((cw2376MarginalSupportedUniverse m).filter
        (fun b => b.1 i = a.1 i)).card ≤ D) :
    (cw2376AllTargetAmbientCollisions m).card ≤
      3 * (cw2376AllExactTargetEdges m).card * D := by
  sorry
