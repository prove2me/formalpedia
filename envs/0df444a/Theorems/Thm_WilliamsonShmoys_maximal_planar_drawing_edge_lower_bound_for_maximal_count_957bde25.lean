-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:46:16.331047+00:00
-- url     : https://prove2.me/theorems/b468113d-c3fa-402b-80b9-2e3fc896649a
-- title:
--   Maximal drawable graphs satisfy the Euler edge lower bound
-- statement:
--   A graph maximal among drawable simple-graph extensions on the same vertex type, with at least three vertices, has at least 3|V|−6 edges. Extend the drawing to a triangulation and use maximality to identify that extension with the original graph; at three vertices the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
