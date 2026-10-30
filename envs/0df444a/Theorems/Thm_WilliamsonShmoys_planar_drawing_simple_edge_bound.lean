-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:53:41.436776+00:00
-- url     : https://prove2.me/theorems/b8085a1e-32af-4e15-a040-0e6b3fe22154
-- title:
--   Simple planar edge bound
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
