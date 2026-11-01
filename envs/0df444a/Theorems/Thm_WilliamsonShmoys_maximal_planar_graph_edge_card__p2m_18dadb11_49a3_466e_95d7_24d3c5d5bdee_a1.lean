-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:54.315297+00:00
-- url     : https://prove2.me/theorems/ad845c85-bbc7-45e1-b337-b2f3a4b80492
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The three-vertex boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
