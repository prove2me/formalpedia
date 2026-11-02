-- Prove2me | Theorems.Thm_maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- name    : maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:18.035189+00:00
-- url     : https://prove2.me/theorems/70fb6007-5dc1-4484-a53d-f6e6d3401839
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V|−6 edges. Prove this by deriving triangulation and the needed connectivity from maximality, then applying planar counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    letI : DecidableRel K.Adj := dK
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by sorry
