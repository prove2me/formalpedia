-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_e7f6fb70
-- name    : WilliamsonShmoys.maximal_drawing_edge_lower_bound_e7f6fb70
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:20:29.009703+00:00
-- url     : https://prove2.me/theorems/42241e15-4ac9-4859-b307-8bc1ff590c7e
-- title:
--   Maximal drawable graphs attain the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least `3n − 6` edges. This supplies the lower-bound half of the target equality. A proof route is to show that maximality forces the embedding to be connected and each face to be triangular: a diagonal through a face between a nonadjacent pair would yield a drawable strict supergraph. Euler’s formula then gives the claimed bound. At three vertices, maximality requires all three edges, so the boundary case is consistent with equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_lower_bound_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : forall Z : SimpleGraph V, Y <= Z ->
      WilliamsonShmoys.HasPlanarDrawingOn Z -> Z = Y) :
    3 * Fintype.card V <= Y.edgeSet.ncard + 6 := by sorry
