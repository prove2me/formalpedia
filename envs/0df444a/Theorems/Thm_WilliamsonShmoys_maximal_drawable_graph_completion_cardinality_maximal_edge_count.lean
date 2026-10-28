-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:46:01.28034+00:00
-- url     : https://prove2.me/theorems/a8cccb55-d478-4044-ba27-16f802829855
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
