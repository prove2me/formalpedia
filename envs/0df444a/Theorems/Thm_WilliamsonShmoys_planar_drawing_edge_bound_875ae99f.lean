-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_875ae99f
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_875ae99f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:35:40.745019+00:00
-- url     : https://prove2.me/theorems/1f6216d4-7176-426b-8eb5-1d4c84c6c67c
-- title:
--   Edge bound for a planar drawing
-- statement:
--   A finite simple graph with a drawing satisfying the bundled crossing-free continuous-arc predicate, and at least three vertices, has at most $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_875ae99f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
