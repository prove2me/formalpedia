-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_nonadjacent_edge
-- name    : WilliamsonShmoys.planar_drawing_add_nonadjacent_edge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:08:51.976636+00:00
-- url     : https://prove2.me/theorems/b567fc7f-58c3-4a12-a7af-2915090cfdd9
-- title:
--   Add one edge between nonadjacent vertices while preserving the drawing
-- statement:
--   Given a crossing-free drawing and a distinct nonadjacent pair, add exactly their edge while keeping the same vertices and a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_nonadjacent_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (huv : u ≠ v)
    (hnot : ¬ G.Adj u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
