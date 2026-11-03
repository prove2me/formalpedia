-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:38.934295+00:00
-- url     : https://prove2.me/theorems/d939f1a9-8524-4bb4-9c19-163885cf3dec
-- title:
--   Same-vertex triangulation extension for a drawable graph
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulation_supergraph__p2m_a2db6ec5_2f79_4623_a999_eb974cadd653_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ G ≤ L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj
         3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
