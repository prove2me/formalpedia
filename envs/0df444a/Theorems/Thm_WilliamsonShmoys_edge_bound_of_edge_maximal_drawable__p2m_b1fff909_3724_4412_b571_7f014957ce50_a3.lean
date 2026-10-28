-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- name    : WilliamsonShmoys.edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:12:48.913875+00:00
-- url     : https://prove2.me/theorems/26108e05-c2fc-4fe9-8d2c-bd306f1fbc83
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal by edge count among drawable supergraphs has exactly 3|V|−6 edges. Prove that maximality forces triangular faces (handling the three-vertex case), then combine Euler’s formula with face-edge incidence counting. This isolates the main planar-topology obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
