-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:27:00.541257+00:00
-- url     : https://prove2.me/theorems/27cf3c3f-e52d-4ff3-ab28-1f4809a4d387
-- title:
--   Maximal planar drawings meet the triangulation edge lower bound
-- statement:
--   An edge-inclusion-maximal graph with the supplied planar drawing on at least three vertices has at least 3n−6 edges. The intended route is to show maximality forces connectivity and triangular faces, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ G.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
