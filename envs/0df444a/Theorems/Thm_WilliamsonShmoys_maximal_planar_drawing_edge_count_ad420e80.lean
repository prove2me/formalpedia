-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_ad420e80
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_ad420e80
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:59:49.504153+00:00
-- url     : https://prove2.me/theorems/b82980ee-3352-4919-98df-dde6a815f9d5
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices that admits the specified crossing-free drawing and is maximal among drawable supergraphs on the same vertex set has exactly 3n − 6 edges. This isolates the graph-theoretic and geometric core needed by the parent; the parent combines the edge count with Euler’s equation using linear arithmetic. A proof route is to show maximality forces a triangulation, then count face-edge incidences and apply Euler’s formula. For n = 3, maximality forces all three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_ad420e80
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
