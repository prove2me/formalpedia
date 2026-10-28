-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_supergraph_step
-- name    : WilliamsonShmoys.planar_drawing_strict_supergraph_step
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T05:01:25.88398+00:00
-- url     : https://prove2.me/theorems/49039170-da5e-4fcd-b925-27780750f53c
-- title:
--   Add an edge to a disconnected planar drawing
-- statement:
--   If a finite ordered vertex graph has a crossing-free drawing and is disconnected, one can add at least one edge to obtain a strict supergraph that still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_strict_supergraph_step
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard < H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
