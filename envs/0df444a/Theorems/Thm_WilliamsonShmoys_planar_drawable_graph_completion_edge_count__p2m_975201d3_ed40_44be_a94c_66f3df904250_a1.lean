-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
-- name    : WilliamsonShmoys.planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:22:33.580841+00:00
-- url     : https://prove2.me/theorems/9329bbd1-6fa9-431d-b5f3-646d0c97c054
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (hHdec : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := hHdec
       3 * Fintype.card V - 6 = H.edgeFinset.card) := by sorry
