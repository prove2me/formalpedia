-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2
-- name    : WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:42.310959+00:00
-- url     : https://prove2.me/theorems/b4fc0ec6-9094-46c1-821a-02fa395e6854
-- title:
--   Drawable graph extends to a triangulation
-- statement:
--   Any drawable finite simple graph with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
