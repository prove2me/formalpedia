-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound_from_arcs
-- name    : WilliamsonShmoys.planar_drawingOn_edge_bound_from_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:25:47.673392+00:00
-- url     : https://prove2.me/theorems/c12bdc62-7d17-4f68-b639-7986bd508587
-- title:
--   Edge bound from an arc-based planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing in the sense of `HasPlanarDrawingOn` has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_edge_bound_from_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
