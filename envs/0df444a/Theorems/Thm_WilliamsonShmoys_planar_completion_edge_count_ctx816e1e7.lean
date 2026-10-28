-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_ctx816e1e7
-- name    : WilliamsonShmoys.planar_completion_edge_count_ctx816e1e7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:03:54.425516+00:00
-- url     : https://prove2.me/theorems/00e208e1-4613-47a9-92ee-becda8e68bb6
-- title:
--   Complete a planar drawing to the triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph with exactly 3|V|−6 edges. The size hypothesis includes the three-vertex boundary, where the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
