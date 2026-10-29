-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:59:34.226604+00:00
-- url     : https://prove2.me/theorems/6be1e368-254d-44b7-8aa7-b4001ba314b4
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. Converting the supplied drawing to a plane embedding, applying Euler’s formula, and counting facial incidences removes the topological upper-bound work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
