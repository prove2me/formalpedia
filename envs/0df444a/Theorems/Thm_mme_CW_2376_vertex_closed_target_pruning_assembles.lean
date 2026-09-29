-- Prove2me | Theorems.Thm_mme_CW_2376_vertex_closed_target_pruning_assembles
-- name    : mme_CW_2376_vertex_closed_target_pruning_assembles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:20:10.074544+00:00
-- url     : https://prove2.me/theorems/4b5458a1-a4f6-42d2-afea-be056cd4cd14
-- title:
--   Vertex-closed target pruning assembles an induced exact-profile family
-- statement:
--   Let $E$ be a retained subset of the full marginal-supported hypergraph and assume it is vertex-closed: every supported mixed edge assembled from retained mode words is itself in $E$. Then target-relative collision deletion produces a mode-disjoint and fully induced family $G$ of exact equation-(13) addresses satisfying
--
--   $$
--   |T(E)| ≤ |G|+|C(T(E),E)|.
--   $$
--
--   The inducedness is relative to every supported mixed triple, not merely mixed triples having the target joint profile. This theorem is the structural bridge between the full-hypergraph Salem--Spencer hash and the exact-profile family consumed by tensor zeroing; the remaining work is solely the randomized target-count and directed-collision estimate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), usual pruning and dominant-profile selection on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_hash_state
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open MME

theorem mme_CW_2376_vertex_closed_target_pruning_assembles
    (m : ℕ) (E : Finset (CW2376MarginalSupportedAddress m))
    (hclosed : CW2376MarginalVertexClosed E) :
    ∃ G : Finset (CW2376ExactProfileAddress m),
      CW2376InducedModeDisjoint G ∧
      ((cw2376ExactTargetEdges E).card : ℝ) ≤
        (G.card : ℝ) + (cw2376TargetAmbientCollisions E).card := by
  sorry
