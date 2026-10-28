-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_same_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:47:44.575574+00:00
-- url     : https://prove2.me/theorems/aa88f872-0354-4fa0-ae0c-fd5a0ff2cf62
-- title:
--   Connect components of a planar drawing on a fixed vertex set
-- statement:
--   Extend a graph with a crossing-free drawing to a connected graph on the same finite ordered vertex type, retaining a crossing-free drawing and at least as many edges. The size hypothesis matches the parent and includes disconnected graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
