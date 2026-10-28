-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_repair3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:50:14.544059+00:00
-- url     : https://prove2.me/theorems/ccf2890e-4dcd-434d-8b85-da2b4841ac38
-- title:
--   Lower edge-count bound for a maximal planar drawing
-- statement:
--   A graph with a `HasPlanarDrawingOn` drawing that is maximal among drawable graphs on the same vertex type and has at least three vertices has at least `3|V| − 6` edges. This removes the parent’s lower-bound obligation; a proof route is to extend a drawing by drawable edges until its faces are triangular, use maximality to exclude a proper extension, and count edges. The three-vertex boundary case must be handled, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) →
      (∀ u v, U.Adj u v → T.Adj u v)) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
