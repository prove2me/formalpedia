-- Prove2me | Theorems.Thm_finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- name    : finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:00.387188+00:00
-- url     : https://prove2.me/theorems/35115ec0-d174-4bc8-b290-cee2e4fcfeda
-- title:
--   Proper simple graph inclusion strictly increases edge count
-- statement:
--   On a finite vertex type, if one simple graph is edge-included in another and the latter has an edge missing from the former, then the latter has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
    {V : Type} [Fintype V]
    (H J : SimpleGraph V)
    (dH : DecidableRel H.Adj) (dJ : DecidableRel J.Adj)
    (hHJ : ∀ u v, H.Adj u v → J.Adj u v)
    (hstrict : ∃ u v, J.Adj u v ∧ ¬ H.Adj u v) :
    (letI : DecidableRel H.Adj := dH
     letI : DecidableRel J.Adj := dJ
     H.edgeFinset.card < J.edgeFinset.card) := by sorry
