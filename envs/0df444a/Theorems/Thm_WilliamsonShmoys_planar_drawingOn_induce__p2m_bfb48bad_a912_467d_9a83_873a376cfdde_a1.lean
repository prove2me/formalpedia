-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- name    : WilliamsonShmoys.planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:39:14.511923+00:00
-- url     : https://prove2.me/theorems/64404299-6c21-4080-966f-7fdd4f629520
-- title:
--   Planar drawing restricts to an induced subgraph
-- statement:
--   Restricting a crossing-free drawing to any finite vertex subset gives a crossing-free drawing of the induced subgraph. The proof restricts the vertex placement and edge arcs, and inherits the drawing properties from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce (↑s : Set V)) := by sorry
