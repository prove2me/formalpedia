-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality
-- name    : WilliamsonShmoys.maximal_drawable_graph_completion_cardinality
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:15:02.897087+00:00
-- url     : https://prove2.me/theorems/1e007d92-6a24-4737-84e9-a5b1a6e8a897
-- title:
--   Drawable completion has the planar triangulation edge count
-- statement:
--   For a drawable simple graph on at least three vertices, there is a drawable supergraph on the same vertex type whose edge count is exactly the planar triangulation count, 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_completion_cardinality
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
