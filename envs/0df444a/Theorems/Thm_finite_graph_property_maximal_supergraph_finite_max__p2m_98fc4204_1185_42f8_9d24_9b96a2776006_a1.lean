-- Prove2me | Theorems.Thm_finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- name    : finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:53:56.449927+00:00
-- url     : https://prove2.me/theorems/f5c79516-2e95-4a0a-99dc-89c9ddb965d5
-- title:
--   Maximum-cardinality feasible supergraph on a finite vertex type
-- statement:
--   For any property of simple graphs on a finite vertex type, a graph satisfying the property has a property-satisfying supergraph whose edge count is at least that of every property-satisfying supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      P H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      (∀ (J : SimpleGraph V) (dJ : DecidableRel J.Adj),
        P J →
        (∀ u v, K.Adj u v → J.Adj u v) →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel J.Adj := dJ
         J.edgeFinset.card ≤ H.edgeFinset.card)) := by sorry
