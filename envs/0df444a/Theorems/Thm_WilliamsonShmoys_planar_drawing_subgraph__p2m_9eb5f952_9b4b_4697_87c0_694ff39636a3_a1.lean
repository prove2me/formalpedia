-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:10.850967+00:00
-- url     : https://prove2.me/theorems/a62d27af-5ba9-435c-bcb7-11a876c6c249
-- title:
--   A subgraph inherits a planar drawing
-- statement:
--   Any spanning subgraph of a graph with a crossing-free drawing has a crossing-free drawing, by retaining the same vertices and arcs and restricting edge conditions to the subgraph’s edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1 {V : Type} [Fintype V] [LinearOrder V] (N K : SimpleGraph V) (hKN : K.edgeSet ⊆ N.edgeSet) (hDrawN : WilliamsonShmoys.HasPlanarDrawingOn N) : WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
