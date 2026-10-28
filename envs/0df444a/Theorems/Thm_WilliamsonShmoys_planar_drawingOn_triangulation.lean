-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:42:07.959074+00:00
-- url     : https://prove2.me/theorems/958a27cf-7f78-4256-83b6-3e08237df0d3
-- title:
--   Triangulate a finite graph with a planar drawing
-- statement:
--   For a finite, linearly ordered vertex type with at least three vertices and a crossing-free drawing, construct a simple planar supergraph on the same vertices whose oriented triangular map has m faces satisfying 2|V| = m + 4.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawingOn_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V), G ≤ H ∧
      ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
        2 * Fintype.card V = m + 4 := by sorry
