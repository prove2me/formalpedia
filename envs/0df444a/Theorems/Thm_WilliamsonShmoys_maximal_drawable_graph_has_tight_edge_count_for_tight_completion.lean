-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_tight_edge_count_for_tight_completion
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_tight_edge_count_for_tight_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:19:57.416417+00:00
-- url     : https://prove2.me/theorems/eb0abcff-07a7-469d-985b-4f77a7414793
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable graphs on its vertex type has exactly $3|V|-6$ edges. The threshold is retained because the edge formula is not the maximal planar edge count in the smaller cases. A proof route is to pass from the supplied drawing to a finite plane embedding, use maximality to show the faces are triangular, then combine Euler's formula with face-edge incidence counting. This contains the main remaining topological and counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_tight_edge_count_for_tight_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
