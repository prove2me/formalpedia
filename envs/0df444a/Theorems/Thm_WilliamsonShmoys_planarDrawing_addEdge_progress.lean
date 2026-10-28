-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_addEdge_progress
-- name    : WilliamsonShmoys.planarDrawing_addEdge_progress
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T05:27:29.496376+00:00
-- url     : https://prove2.me/theorems/bd6ebce6-a078-4d66-baef-72b77f77cf24
-- title:
--   Extend a disconnected planar drawing by an edge
-- statement:
--   Every disconnected graph on a finite ordered vertex type with a crossing-free drawing has a strictly larger same-vertex supergraph that also has a crossing-free drawing. A proof can choose vertices in different components, then construct a simple joining arc through the complement of the finite embedded graph and add its edge while retaining the old drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_addEdge_progress
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊂ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
