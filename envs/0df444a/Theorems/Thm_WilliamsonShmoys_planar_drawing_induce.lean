-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce
-- name    : WilliamsonShmoys.planar_drawing_induce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:58:44.91043+00:00
-- url     : https://prove2.me/theorems/8e57a5ae-69cb-4cfe-b4d4-e34f510f384d
-- title:
--   Planar drawing passes to induced subgraphs on finite sets
-- statement:
--   Restricting a graph with the stated planar drawing to the vertices of a finite set preserves such a drawing, using the original point and arc maps and the fact that every induced edge was already an edge of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce (↑S : Set V)) := by sorry
