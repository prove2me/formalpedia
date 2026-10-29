-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_on_finite_type
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_on_finite_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:10:23.208407+00:00
-- url     : https://prove2.me/theorems/62aa0e06-ad06-434c-b965-3e75ba9f4ca7
-- title:
--   Edge count of a maximal planar drawing on a finite vertex type
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_on_finite_type
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
