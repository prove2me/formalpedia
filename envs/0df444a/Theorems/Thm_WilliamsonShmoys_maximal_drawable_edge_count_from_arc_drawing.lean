-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_from_arc_drawing
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_from_arc_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:14:44.944837+00:00
-- url     : https://prove2.me/theorems/9039209a-4dfe-4d0e-bff1-66b656f6ae53
-- title:
--   Edge count of a maximal graph with an arc drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_from_arc_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
